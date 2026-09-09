# -*- coding: utf-8 -*-
r"""
Soluções Fiscais — Captura automática de NFS-e (Padrão Nacional)

Aplicativo desktop:
  1. Lista os certificados digitais A1 instalados no Windows (CurrentUser\My);
  2. O usuário seleciona um ou mais certificados e busca os XMLs no ADN
     (Ambiente de Dados Nacional do Sistema Nacional NFS-e), de forma
     incremental, para uma pasta geral;
  3. O usuário escolhe uma competência (mês/ano): os XMLs daquela competência
     são copiados para uma pasta própria e é gerada uma planilha Excel com
     todos os campos das notas, incluindo a aba de apresentação da empresa.

Licenciamento: na abertura é exigido um código no formato SF-AAAAMMDD-XXXXXXXXXX
(gerado pelo gerador_chave.py, que NAO deve ser distribuído ao cliente).
A data embutida no código define até quando a licença vale.

A captura usa o certificado direto do repositório do Windows via PowerShell/
SChannel: a chave privada nunca é lida nem exportada pelo programa.
"""

import csv
import hashlib
import hmac
import json
import os
import queue
import re
import shutil
import subprocess
import sys
import threading
import urllib.request
import xml.etree.ElementTree as ET
from datetime import date, datetime
from pathlib import Path

APP_NOME = "Soluções Fiscais"
APP_TITULO = "Soluções Fiscais — Captura NFS-e (Padrão Nacional)"
# Segredo da licença, ofuscado (montado em tempo de execução por XOR de duas
# constantes) para nao aparecer numa varredura simples de strings do executavel.
_PARTE_A = bytes.fromhex("418f84807c70bb78330dba05690283c9ed0c2fbc8e51e91d9003767d43fac188e69d")
_PARTE_B = bytes.fromhex("12e0e8f51f1fde0b7564c966086bf0eadf3c1d8ad270877be366363f11d7f6bf85ac")
SEGREDO = bytes(a ^ b for a, b in zip(_PARTE_A, _PARTE_B))

PASTA_APP = Path.home() / "AppData" / "Roaming" / "SolucoesFiscais"
ARQ_LICENCA = PASTA_APP / "ativacao.json"
ARQ_CONFIG = PASTA_APP / "config.json"
ARQ_LICENCA_ONLINE = PASTA_APP / "licenca_online.json"
# Validação ONLINE da chave: o programa consulta este endereço para saber se a
# chave foi revogada (ex.: código repassado a terceiros). O arquivo licencas.json
# é gerado/assinado pelo gerador_chave.py (--revogar) e publicado na hospedagem
# do site. Sem internet ou sem o arquivo publicado, o programa segue funcionando
# (fail-open) — a revogação é bloqueio adicional, não ponto único de falha.
URL_LICENCAS = "https://www.solucoesfiscais.com.br/licencas.json"
NOME_PASTA_NSU = "Ultimo NSU"


def pasta_documentos() -> Path:
    """Pasta Documentos real do usuário NESTE computador, resolvida pelo
    próprio Windows (SHGetKnownFolderPath) — funciona com Windows em outros
    idiomas e com Documentos redirecionado (ex.: OneDrive).
    Fallback: pasta pessoal\\Documents."""
    try:
        import ctypes
        from ctypes import wintypes

        class _GUID(ctypes.Structure):
            _fields_ = [("Data1", wintypes.DWORD), ("Data2", wintypes.WORD),
                        ("Data3", wintypes.WORD), ("Data4", ctypes.c_ubyte * 8)]

        # FOLDERID_Documents {FDD39AD0-238F-46AF-ADB4-6C85480369C7}
        guid = _GUID(0xFDD39AD0, 0x238F, 0x46AF,
                     (ctypes.c_ubyte * 8)(0xAD, 0xB4, 0x6C, 0x85, 0x48, 0x03, 0x69, 0xC7))
        caminho = ctypes.c_wchar_p()
        if ctypes.windll.shell32.SHGetKnownFolderPath(
                ctypes.byref(guid), 0, None, ctypes.byref(caminho)) == 0 and caminho.value:
            pasta = Path(caminho.value)
            ctypes.windll.ole32.CoTaskMemFree(caminho)
            return pasta
    except Exception:
        pass
    return Path.home() / "Documents"


def pasta_geral_base() -> Path:
    """Pasta base FIXA do programa: Documentos\\SolucoesFiscais do computador
    onde está rodando. Tudo fica dentro dela — pastas por empresa, Planilhas
    Agrupadas e o Ultimo NSU — sem depender de configuração salva, para que
    o mesmo exe funcione em qualquer máquina."""
    base = pasta_documentos() / "SolucoesFiscais"
    base.mkdir(parents=True, exist_ok=True)
    return base


def _caminho_programa() -> Path:
    """Caminho real do programa: o .exe distribuído ou este .py.

    No exe onefile (Nuitka), sys.executable e __file__ apontam para a pasta
    temporária de extração — apagada quando o programa fecha. O caminho
    verdadeiro do exe vem de __compiled__.original_argv0 / sys.argv[0];
    qualquer candidato dentro de %TEMP% é descartado."""
    compilado = globals().get("__compiled__")
    candidatos = []
    if compilado is not None or getattr(sys, "frozen", False):
        candidatos += [getattr(compilado, "original_argv0", None), sys.argv[0], sys.executable]
    candidatos.append(__file__)
    temp = os.environ.get("TEMP", "")
    raiz_temp = (str(Path(temp).resolve()).lower() + os.sep) if temp else None
    for candidato in candidatos:
        if not candidato:
            continue
        caminho = Path(candidato).resolve()
        if raiz_temp and str(caminho).lower().startswith(raiz_temp):
            continue
        if caminho.is_file():
            return caminho
    return Path(__file__).resolve()


def pasta_nsu() -> Path:
    """Pasta central "Ultimo NSU", dentro da pasta base (Documentos\\SolucoesFiscais).

    Guarda o último NSU baixado de cada CNPJ em ultimo_nsu_<cnpj>.txt: a
    próxima captura continua a partir desse número, em qualquer computador,
    independentemente de onde o exe estiver. Sem esse registro, a captura
    baixa a base inteira desde o NSU 0."""
    pasta = pasta_geral_base() / NOME_PASTA_NSU
    pasta.mkdir(parents=True, exist_ok=True)
    return pasta


def _ler_nsu(arquivo: Path) -> int:
    """Lê o NSU de um txt de progresso; 0 se não existir ou estiver inválido."""
    try:
        return int(arquivo.read_text(encoding="ascii", errors="ignore").strip() or 0)
    except (OSError, ValueError):
        return 0

CRIAR_SEM_JANELA = 0x08000000  # CREATE_NO_WINDOW (não abrir console ao chamar PowerShell)


# ----------------------------------------------------------------------------
# Licença
# ----------------------------------------------------------------------------

def codigo_maquina() -> str:
    """Identificador desta máquina (derivado do MachineGuid do Windows).
    Usado internamente para lacrar a ativação no computador — o cliente
    não precisa informar nada."""
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Microsoft\Cryptography") as chave_reg:
            guid = winreg.QueryValueEx(chave_reg, "MachineGuid")[0]
    except Exception:
        guid = os.environ.get("COMPUTERNAME", "desconhecido")
    resumo = hmac.new(SEGREDO, f"MAQ|{guid}".encode(), hashlib.sha256).hexdigest()[:8].upper()
    return f"{resumo[:4]}-{resumo[4:]}"


def assinatura(payload: str) -> str:
    return hmac.new(SEGREDO, f"SF|{payload}".encode(), hashlib.sha256).hexdigest()[:10].upper()


# E = Essencial (1 CNPJ), O = Escritório (até 10 CNPJs). Adicione aqui se
# um novo plano surgir — o resto do código lê sempre deste dicionário.
LIMITES_PLANO = {"E": 1, "O": 10}


def gerar_chave(validade: date, plano: str = "E") -> str:
    plano = (plano or "E").strip().upper()
    if plano not in LIMITES_PLANO:
        plano = "E"
    payload = f"{plano}-{validade.strftime('%Y%m%d')}"
    return f"SF-{payload}-{assinatura(payload)}"


def validar_chave(codigo: str):
    """Retorna (data_validade, plano) embutidos no código, ou None se inválido."""
    m = re.fullmatch(r"SF-([EO])-(\d{8})-([0-9A-F]{10})", (codigo or "").strip().upper())
    if not m:
        return None
    plano, data_str, assinado = m.groups()
    payload = f"{plano}-{data_str}"
    if not hmac.compare_digest(assinatura(payload), assinado):
        return None
    try:
        validade = date(int(data_str[:4]), int(data_str[4:6]), int(data_str[6:8]))
    except ValueError:
        return None
    return validade, plano


def _lacre_ativacao(codigo: str, maquina: str) -> str:
    return hmac.new(SEGREDO, f"ATIV|{codigo}|{maquina}".encode(),
                    hashlib.sha256).hexdigest()[:16].upper()


def _hash_chave(codigo: str) -> str:
    return hashlib.sha256(f"CHV|{(codigo or '').strip().upper()}".encode()).hexdigest()


def _assinatura_revogadas(revogadas) -> str:
    corpo = ",".join(sorted(revogadas))
    return hmac.new(SEGREDO, f"REV|{corpo}".encode(), hashlib.sha256).hexdigest()


def consultar_revogacao_online(codigo: str):
    """Consulta a lista de chaves revogadas publicada em URL_LICENCAS.

    Retorna "revogada", "ok" (consultou e a chave não está revogada) ou None
    (lista indisponível/ilegível — sem internet, hospedagem fora do ar etc.).
    A lista é assinada com o segredo do produto: apontar o endereço para outro
    servidor (hosts/proxy) não permite forjar uma lista que o programa aceite."""
    try:
        with urllib.request.urlopen(URL_LICENCAS, timeout=6) as resposta:
            dados = json.loads(resposta.read().decode("utf-8"))
        revogadas = [str(r) for r in dados.get("revogadas", [])]
        if not hmac.compare_digest(_assinatura_revogadas(revogadas),
                                   str(dados.get("assinatura", ""))):
            return None  # lista adulterada/ilegível: ignora
        return "revogada" if _hash_chave(codigo) in revogadas else "ok"
    except Exception:
        return None


def _situacao_online_com_cache(codigo: str) -> str:
    """Verificação online com cache local: consulta no máximo 1x por dia
    (ou a cada 6h enquanto a lista estiver indisponível), para não atrasar
    a abertura do programa nem depender da internet a cada uso."""
    agora = datetime.now().timestamp()
    try:
        cache = json.loads(ARQ_LICENCA_ONLINE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        cache = {}
    if cache.get("chave") == _hash_chave(codigo):
        idade = agora - float(cache.get("quando", 0) or 0)
        validade_cache = 86400 if cache.get("situacao") in ("ok", "revogada") else 21600
        if 0 <= idade < validade_cache:
            return cache.get("situacao", "indisponivel")
    situacao = consultar_revogacao_online(codigo) or "indisponivel"
    try:
        PASTA_APP.mkdir(parents=True, exist_ok=True)
        ARQ_LICENCA_ONLINE.write_text(json.dumps({
            "chave": _hash_chave(codigo), "situacao": situacao, "quando": agora,
        }), encoding="utf-8")
    except OSError:
        pass
    return situacao


def guardar_licenca(codigo: str):
    """Ativa a chave NESTE computador: grava um lacre amarrado ao identificador
    da máquina. O arquivo de ativação copiado para outro PC não funciona."""
    codigo = codigo.strip().upper()
    maquina = codigo_maquina()
    PASTA_APP.mkdir(parents=True, exist_ok=True)
    ARQ_LICENCA.write_text(json.dumps({
        "codigo": codigo,
        "maquina": maquina,
        "lacre": _lacre_ativacao(codigo, maquina),
    }), encoding="utf-8")


def licenca_armazenada():
    """Valida a ativação local: chave íntegra, dentro da validade e lacrada
    na máquina onde foi ativada. Retorna (validade, plano) ou None."""
    if not ARQ_LICENCA.is_file():
        return None
    try:
        dados = json.loads(ARQ_LICENCA.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None
    maquina = codigo_maquina()
    if dados.get("maquina") != maquina:
        return None
    if not hmac.compare_digest(_lacre_ativacao(dados.get("codigo", ""), maquina),
                               dados.get("lacre", "")):
        return None
    resultado = validar_chave(dados.get("codigo", ""))
    if resultado is not None and _situacao_online_com_cache(dados.get("codigo", "")) == "revogada":
        return None  # revogada na validação online (ex.: código repassado a terceiros)
    return resultado


# ----------------------------------------------------------------------------
# Certificados instalados (via PowerShell — a chave privada fica no Windows)
# ----------------------------------------------------------------------------

def listar_certificados():
    comando = (
        "[Console]::OutputEncoding=[Text.Encoding]::UTF8; "
        "Get-ChildItem Cert:\\CurrentUser\\My | "
        "Where-Object { $_.HasPrivateKey -and $_.NotAfter -gt (Get-Date) } | "
        "ForEach-Object { [pscustomobject]@{ T=$_.Thumbprint; S=$_.Subject; "
        "N=$_.NotAfter.ToString('yyyy-MM-dd') } } | ConvertTo-Json -Compress"
    )
    r = subprocess.run(
        ["powershell", "-NoProfile", "-Command", comando],
        capture_output=True, creationflags=CRIAR_SEM_JANELA,
    )
    saida = r.stdout.decode("utf-8", errors="replace").strip()
    if not saida:
        return []
    dados = json.loads(saida)
    if isinstance(dados, dict):
        dados = [dados]
    certificados = []
    for item in dados:
        assunto = item.get("S", "")
        cnpj = re.search(r":(\d{14})", assunto)
        nome = re.search(r"CN=([^,:]+)", assunto)
        if not cnpj:
            continue  # ignora certificados que nao sao e-CNPJ (ex.: certificados de maquina)
        certificados.append({
            "thumbprint": item.get("T", ""),
            "cnpj": cnpj.group(1),
            "nome": (nome.group(1) if nome else assunto).strip(),
            "validade": item.get("N", ""),
        })
    certificados.sort(key=lambda c: (c["nome"], c["cnpj"]))
    return certificados


# ----------------------------------------------------------------------------
# Motor de captura (PowerShell) — mesmo fluxo homologado do processo original
# ----------------------------------------------------------------------------

MOTOR_PS1 = r'''
param([string]$Thumbprint, [string]$PastaXml, [string]$ArqNsu)
$ErrorActionPreference = "Stop"
try { [Console]::OutputEncoding = [Text.Encoding]::UTF8 } catch {}
# TLS 1.2 sempre; TLS 1.3 entra junto quando o Windows/.NET oferecem
$protocolos = [Net.SecurityProtocolType]::Tls12
try { $protocolos = $protocolos -bor [Net.SecurityProtocolType]::Tls13 } catch {}
try { [Net.ServicePointManager]::SecurityProtocol = $protocolos }
catch { [Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12 }
$base = "https://adn.nfse.gov.br"

function Falha([string]$mensagem) { Write-Output "ERRO $mensagem"; exit 1 }

New-Item -ItemType Directory -Force $PastaXml | Out-Null
try { $cert = Get-Item "Cert:\CurrentUser\My\$Thumbprint" }
catch { Falha "certificado não encontrado no Windows (foi removido ou reinstalado?). Abra o programa e selecione o certificado novamente." }
if ($cert.NotAfter -lt (Get-Date)) {
    Falha ("o certificado venceu em {0:dd/MM/yyyy}. Renove o certificado digital e selecione-o novamente no programa." -f $cert.NotAfter)
}
if (-not $cert.HasPrivateKey) {
    Falha "o certificado está instalado sem a chave privada. Reinstale o arquivo do certificado A1 (.pfx) neste Windows."
}
try {
    $chave = [Security.Cryptography.X509Certificates.RSACertificateExtensions]::GetRSAPrivateKey($cert)
    if ($chave) { $chave.Dispose() }
} catch {
    Falha "o Windows não conseguiu acessar a chave privada do certificado. Se for A3 (token/cartão), conecte o dispositivo; se for A1, reinstale o arquivo .pfx do certificado."
}
$nsu = [long]0
if (Test-Path $ArqNsu) {
    $bruto = "$(Get-Content $ArqNsu -TotalCount 1)".Trim()
    if ($bruto -match '^\d+$') { $nsu = [long]$bruto }
}
Write-Output "INICIO NSU=$nsu"
$total = 0
$falhasConexao = 0
while ($true) {
    $url = "$base/contribuintes/DFe/${nsu}?lote=true"
    try {
        $r = Invoke-WebRequest -Uri $url -Certificate $cert -UseBasicParsing -TimeoutSec 120
    } catch {
        $msg = ("$($_.Exception.Message)" -replace '\s+', ' ').Trim()
        $code = 0
        if ($_.Exception.Response) { $code = [int]$_.Exception.Response.StatusCode }
        if ($code -eq 404) { break }
        if ($code -eq 429) { Start-Sleep 15; continue }
        if ($code -eq 496) { Falha "o portal não recebeu o certificado digital (HTTP 496). Reinstale o certificado A1 (.pfx) neste Windows e tente de novo." }
        if ($code -ne 0) { Falha "o portal respondeu com erro HTTP $code ($msg)." }
        # code 0: a conexão falhou antes de chegar ao portal (ex.: canal SSL/TLS);
        # tenta de novo algumas vezes antes de diagnosticar de que lado está o problema
        $falhasConexao++
        if ($falhasConexao -lt 4) { Start-Sleep 5; continue }
        $alcancouPortal = $true
        try { Invoke-WebRequest -Uri $base -UseBasicParsing -TimeoutSec 30 | Out-Null }
        catch { if (-not $_.Exception.Response) { $alcancouPortal = $false } }
        if ($alcancouPortal) {
            Falha "a conexão segura falha somente quando o certificado digital é usado ($msg). Causas mais comuns, nesta ordem: 1) antivírus com inspeção de tráfego HTTPS/SSL ligada — desative essa opção no antivírus (ou inclua exceção para adn.nfse.gov.br); 2) chave privada inacessível — reinstale o certificado A1 (.pfx); 3) certificado A3 sem o token/cartão conectado."
        }
        Falha "o computador não conseguiu completar nenhuma conexão segura com o portal ($msg). Verifique a data e hora do Windows, a conexão com a internet e o antivírus/proxy da rede."
    }
    $falhasConexao = 0
    $corpo = $r.Content | ConvertFrom-Json
    $lote = @($corpo.LoteDFe)
    if ($lote.Count -eq 0) { break }
    foreach ($doc in $lote) {
        $bytes = [Convert]::FromBase64String($doc.ArquivoXml)
        try {
            $ms = New-Object IO.MemoryStream(, $bytes)
            $gz = New-Object IO.Compression.GzipStream($ms, [IO.Compression.CompressionMode]::Decompress)
            $sr = New-Object IO.StreamReader($gz, [Text.Encoding]::UTF8)
            $xml = $sr.ReadToEnd()
        } catch { $xml = [Text.Encoding]::UTF8.GetString($bytes) }
        $nome = "{0:D8}_{1}_{2}.xml" -f [long]$doc.NSU, $doc.TipoDocumento, $doc.ChaveAcesso
        [IO.File]::WriteAllText((Join-Path $PastaXml $nome), $xml)
        if ([long]$doc.NSU -gt $nsu) { $nsu = [long]$doc.NSU }
        $total++
    }
    Write-Output "LOTE $($lote.Count) NSU=$nsu"
    Set-Content -Path $ArqNsu -Value $nsu -Encoding Ascii
    Start-Sleep -Seconds 1
}
Write-Output "FIM TOTAL=$total NSU=$nsu"
'''


def caminho_motor() -> Path:
    PASTA_APP.mkdir(parents=True, exist_ok=True)
    destino = PASTA_APP / "motor_captura.ps1"
    # utf-8-sig (com BOM): sem o BOM o PowerShell 5.1 lê o arquivo como ANSI
    # e corrompe os acentos das mensagens de diagnóstico
    destino.write_text(MOTOR_PS1, encoding="utf-8-sig")
    return destino


def capturar_certificado(cert: dict, pasta_geral: Path, log):
    base = pasta_empresa(pasta_geral, cert["cnpj"], cert["nome"])
    pasta_xml = pasta_completa(base)
    identificador = cert["cnpj"] or cert["thumbprint"]
    arq_nsu = pasta_nsu() / f"ultimo_nsu_{identificador}.txt"
    arq_nsu_empresa = base / f"ultimo_nsu_{identificador}.txt"
    # retoma do maior NSU já registrado: pasta central "Ultimo NSU" (na pasta
    # base em Documentos), txt antigo na pasta da empresa ou o local legado
    # ao lado do exe (versões anteriores). Sem registro, baixa a base inteira.
    arq_nsu_legado = _caminho_programa().parent / NOME_PASTA_NSU / f"ultimo_nsu_{identificador}.txt"
    nsu_inicial = max(_ler_nsu(arq_nsu), _ler_nsu(arq_nsu_empresa), _ler_nsu(arq_nsu_legado))
    if nsu_inicial:
        arq_nsu.write_text(str(nsu_inicial), encoding="ascii")
    processo = subprocess.Popen(
        ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass",
         "-File", str(caminho_motor()),
         "-Thumbprint", cert["thumbprint"],
         "-PastaXml", str(pasta_xml), "-ArqNsu", str(arq_nsu)],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        creationflags=CRIAR_SEM_JANELA,
    )
    comecou_do_zero, houve_erro, total_baixado = False, False, None
    for linha_bruta in processo.stdout:
        linha = linha_bruta.decode("utf-8", errors="replace").strip()
        if linha.startswith("LOTE"):
            log(f"   {cert['cnpj']}: {linha.split('NSU=')[-1]} documentos acumulados...")
        elif linha.startswith("FIM"):
            m = re.search(r"TOTAL=(\d+)", linha)
            total_baixado = int(m.group(1)) if m else None
            log(f"   {cert['cnpj']}: {total_baixado if total_baixado is not None else '?'} documento(s) novo(s).")
        elif linha.startswith("INICIO"):
            nsu_texto = linha.split("=")[-1]
            comecou_do_zero = nsu_texto == "0"
            if comecou_do_zero:
                log(f"   {cert['cnpj']}: sem NSU anterior — baixando a base inteira.")
            else:
                log(f"   {cert['cnpj']}: continuando do NSU {nsu_texto}")
        elif linha.startswith("ERRO"):
            houve_erro = True
            log(f"   {cert['cnpj']}: ERRO — {linha[4:].strip()}")
        elif linha:
            log(f"   {cert['cnpj']}: {linha}")
    processo.wait()
    if comecou_do_zero and total_baixado == 0 and not houve_erro:
        log(f"   {cert['cnpj']}: a conexão com o Portal Nacional funcionou, mas não há NENHUM "
            "documento disponível para este CNPJ no ambiente nacional. Causa mais comum: o "
            "município do prestador ainda não aderiu à NFS-e do padrão nacional (as notas ficam "
            "só no sistema da prefeitura). Confira em www.gov.br/nfse se o município é conveniado.")
    # espelha o NSU final na pasta da empresa: mantém o CNPJ marcado como
    # monitorado (cnpjs_capturados) e deixa o número visível junto aos XMLs
    arq_nsu_empresa.write_text(str(_ler_nsu(arq_nsu)), encoding="ascii")
    return base


# ----------------------------------------------------------------------------
# Índice local dos XMLs (para competência ser rápida mesmo com muitos arquivos)
# ----------------------------------------------------------------------------

CAMPOS_INDICE = ["arquivo", "tipo", "chave", "competencia", "emissao", "toma", "prest", "interm",
                 "numero", "prestador", "tomador"]

MESES_NOME = {1: "01 - Janeiro", 2: "02 - Fevereiro", 3: "03 - Março", 4: "04 - Abril",
              5: "05 - Maio", 6: "06 - Junho", 7: "07 - Julho", 8: "08 - Agosto",
              9: "09 - Setembro", 10: "10 - Outubro", 11: "11 - Novembro", 12: "12 - Dezembro"}


TIPOS_SERVICO = {"tomados": "Serviços Tomados", "prestados": "Serviços Prestados"}


def estrutura_pastas(base_empresa: Path, tipo: str = "tomados") -> dict:
    originais = base_empresa / "Originais"
    ramo = originais / TIPOS_SERVICO[tipo]
    return {
        "completo": originais / "Período Completo",
        "xml": ramo / "XML por período",
        "pdf": ramo / "PDF por período",
        "planilhas": ramo / "Planilhas",
    }


def pasta_completa(base_empresa: Path) -> Path:
    r"""Pasta única com todos os XMLs capturados (tomados e prestados vêm no
    mesmo fluxo do ADN); migra automaticamente os locais antigos."""
    destino = estrutura_pastas(base_empresa)["completo"]
    if not destino.is_dir():
        for legado in (base_empresa / "Originais" / "Serviços Tomados" / "Período Completo",
                       base_empresa / "xmls"):
            if legado.is_dir():
                destino.parent.mkdir(parents=True, exist_ok=True)
                legado.rename(destino)
                break
    destino.mkdir(parents=True, exist_ok=True)
    return destino


def pasta_empresa(pasta_geral: Path, cnpj: str, nome: str) -> Path:
    """Pasta-base da empresa (CNPJ - Razão Social) dentro da pasta geral.
    Se já existir, é reaproveitada."""
    rotulo = re.sub(r'[\\/:*?"<>|]', "", f"{cnpj} - {nome}").strip()[:120]
    base = pasta_geral / rotulo
    base.mkdir(parents=True, exist_ok=True)
    return base


def pastas_empresas_existentes(pasta_geral: Path):
    if not pasta_geral.is_dir():
        return []
    return sorted(p for p in pasta_geral.iterdir()
                  if p.is_dir() and re.match(r"\d{14} - ", p.name))


def _local(tag):
    return tag.rsplit("}", 1)[-1]


def _achar(raiz, nome):
    for el in raiz.iter():
        if _local(el.tag) == nome:
            return el
    return None


def _texto(raiz, pai, nome):
    alvo = _achar(raiz, pai)
    if alvo is None:
        return ""
    filho = _achar(alvo, nome)
    return (filho.text or "").strip() if filho is not None else ""


def atualizar_indice(pasta_geral: Path, log):
    pasta_xml = pasta_completa(pasta_geral)
    arq_indice = pasta_geral / "indice.csv"
    indice = {}
    if arq_indice.is_file():
        with open(arq_indice, encoding="utf-8") as arq:
            leitor = csv.DictReader(arq, delimiter=";")
            if leitor.fieldnames == CAMPOS_INDICE:
                for linha in leitor:
                    indice[linha["arquivo"]] = linha
            else:
                log("   índice em formato antigo — reindexando tudo (uma única vez).")

    novos = 0
    for arquivo in pasta_xml.glob("*.xml"):
        if arquivo.name in indice:
            continue
        m = re.match(r"\d{8}_(\w+)_(\d{50})\.xml$", arquivo.name)
        if not m:
            continue
        tipo, chave = m.groups()
        registro = {c: "" for c in CAMPOS_INDICE}
        registro.update(arquivo=arquivo.name, tipo=tipo, chave=chave)
        if tipo == "NFSE":
            try:
                raiz = ET.parse(arquivo).getroot()
            except ET.ParseError:
                continue
            inf_dps = _achar(raiz, "infDPS") or raiz
            registro["competencia"] = _texto(raiz, "infDPS", "dCompet")[:7]
            registro["emissao"] = _texto(raiz, "infDPS", "dhEmi")[:10]
            registro["toma"] = _texto(inf_dps, "toma", "CNPJ")
            registro["prest"] = _texto(inf_dps, "prest", "CNPJ")
            registro["interm"] = _texto(inf_dps, "interm", "CNPJ")
            registro["numero"] = _texto(raiz, "infNFSe", "nNFSe")
            registro["prestador"] = _texto(raiz, "emit", "xNome") or _texto(inf_dps, "prest", "xNome")
            registro["tomador"] = _texto(inf_dps, "toma", "xNome")
        indice[arquivo.name] = registro
        novos += 1
        if novos % 5000 == 0:
            log(f"   indexando... {novos} novos")

    if novos:
        with open(arq_indice, "w", newline="", encoding="utf-8") as arq:
            escritor = csv.DictWriter(arq, fieldnames=CAMPOS_INDICE, delimiter=";")
            escritor.writeheader()
            escritor.writerows(indice.values())
    log(f"   índice atualizado: {len(indice)} documentos ({novos} novos).")
    return list(indice.values())


def cnpjs_capturados(pasta_geral: Path):
    return {m.group(1) for p in pasta_geral.glob("ultimo_nsu_*.txt")
            if (m := re.match(r"ultimo_nsu_(\d{14})\.txt$", p.name))}


def situacao_por_eventos(base_empresa: Path) -> dict:
    """Mapa chave de acesso -> "Cancelada"/"Substituída", a partir dos XMLs de
    evento em Período Completo (arquivos com tipo diferente de NFSE no nome).
    O cancelamento chega pelo ADN como evento novo, com NSU próprio — por isso
    a captura incremental já traz a situação atualizada de notas antigas."""
    situacoes = {}
    for arquivo in pasta_completa(base_empresa).glob("*.xml"):
        m = re.match(r"\d{8}_(\w+)_(\d{50})\.xml$", arquivo.name)
        if not m or m.group(1) == "NFSE":
            continue
        try:
            dados = arquivo.read_bytes()
        except OSError:
            continue
        if b"anc" in dados:
            situacoes[m.group(2)] = "Cancelada"
        elif b"ubst" in dados and situacoes.get(m.group(2)) != "Cancelada":
            situacoes[m.group(2)] = "Substituída"
    return situacoes


# ----------------------------------------------------------------------------
# Planilha Excel (todos os campos + aba de apresentação)
# ----------------------------------------------------------------------------

RE_CONTROLE = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f]")
RE_DECIMAL = re.compile(r"^-?\d+\.\d+$")


def _registrar(saida, coluna, valor):
    if coluna in saida:
        i = 2
        while f"{coluna}[{i}]" in saida:
            i += 1
        coluna = f"{coluna}[{i}]"
    valor = RE_CONTROLE.sub("", valor)
    saida[coluna] = float(valor) if RE_DECIMAL.match(valor) else valor


def _achatar(elemento, caminho, saida):
    nome = _local(elemento.tag)
    if nome == "Signature":
        return
    caminho = f"{caminho}.{nome}" if caminho else nome
    for atributo, valor in elemento.attrib.items():
        _registrar(saida, f"{caminho}@{_local(atributo)}", valor)
    texto = (elemento.text or "").strip()
    if texto and len(elemento) == 0:
        _registrar(saida, caminho, texto)
    for filho in elemento:
        _achatar(filho, caminho, saida)


CONTATOS = [
    "✉   contato@solucoesfiscais.com.br",
    "🌐  www.solucoesfiscais.com.br",
    "📱  (51) 99999-9999",
]

COR_AZUL = "1F3864"
COR_VERDE = "375623"


def desenhar_robo(destino: Path):
    """Desenha o robô da capa (estilo flat: branco, azul-marinho e ciano)."""
    try:
        from PIL import Image, ImageDraw
    except ImportError:
        return None
    imagem = Image.new("RGBA", (480, 620), (0, 0, 0, 0))
    d = ImageDraw.Draw(imagem)
    navy = (31, 56, 100, 255)
    branco = (250, 250, 252, 255)
    ciano = (127, 209, 255, 255)
    visor = (23, 34, 59, 255)
    traco = 6
    # antena
    d.line([(240, 60), (240, 100)], fill=navy, width=traco)
    d.ellipse([(226, 34), (254, 62)], fill=ciano, outline=navy, width=4)
    # braço esquerdo levantado (acenando) com mão
    d.rounded_rectangle([(52, 150), (102, 300)], radius=25, fill=branco, outline=navy, width=traco)
    d.ellipse([(42, 104), (112, 174)], fill=branco, outline=navy, width=traco)
    # cabeça e visor
    d.rounded_rectangle([(120, 100), (360, 262)], radius=60, fill=branco, outline=navy, width=traco)
    d.rounded_rectangle([(150, 130), (330, 232)], radius=42, fill=visor)
    d.ellipse([(186, 158), (224, 196)], fill=ciano)
    d.ellipse([(256, 158), (294, 196)], fill=ciano)
    d.arc([(206, 172), (274, 216)], start=25, end=155, fill=ciano, width=6)
    # braço direito abaixado
    d.rounded_rectangle([(356, 300), (408, 452)], radius=25, fill=branco, outline=navy, width=traco)
    # corpo e peito
    d.rounded_rectangle([(138, 280), (342, 472)], radius=52, fill=branco, outline=navy, width=traco)
    d.rounded_rectangle([(190, 320), (290, 402)], radius=22, fill=ciano, outline=navy, width=4)
    # pernas
    d.rounded_rectangle([(172, 482), (224, 574)], radius=24, fill=branco, outline=navy, width=traco)
    d.rounded_rectangle([(256, 482), (308, 574)], radius=24, fill=branco, outline=navy, width=traco)
    imagem.save(destino)
    return destino


def montar_apresentacao(wb, competencia, cartoes_dados, cnpjs):
    from openpyxl.styles import Alignment, Font, PatternFill
    from openpyxl.utils import get_column_letter, range_boundaries

    ws = wb.create_sheet("Apresentação", 0)
    ws.sheet_view.showGridLines = False

    OURO = "F2A900"
    AZUL_CLARO = "EAF1FB"
    FONTE = "Segoe UI"
    esquerda = Alignment(horizontal="left", vertical="center", wrap_text=True)
    centro = Alignment(horizontal="center", vertical="center", wrap_text=True)

    for coluna in range(1, 23):  # A..V
        ws.column_dimensions[get_column_letter(coluna)].width = 3.6

    def pintar(faixa, cor):
        col_ini, lin_ini, col_fim, lin_fim = range_boundaries(faixa)
        fundo = PatternFill("solid", fgColor=cor)
        for linha in range(lin_ini, lin_fim + 1):
            for coluna in range(col_ini, col_fim + 1):
                ws.cell(row=linha, column=coluna).fill = fundo

    def caixa(faixa, texto, fonte, alinhamento=esquerda, cor_fundo=None):
        if cor_fundo:
            pintar(faixa, cor_fundo)
        ws.merge_cells(faixa)
        celula = ws[faixa.split(":")[0]]
        celula.value = texto
        celula.font = fonte
        celula.alignment = alinhamento

    alturas = {1: 6, 2: 26, 3: 6, 4: 10, 5: 26, 6: 26, 7: 26, 8: 26, 9: 4, 10: 18, 11: 6,
               12: 5, 13: 10, 14: 20, 15: 4, 16: 20, 17: 4, 18: 20, 19: 12, 20: 16, 21: 30,
               22: 15, 23: 10, 24: 34, 25: 16, 26: 16, 27: 16, 28: 18, 29: 8, 30: 18, 31: 18}
    for linha, altura in alturas.items():
        ws.row_dimensions[linha].height = altura

    # faixa superior
    pintar("A1:V3", COR_AZUL)
    caixa("B2:V2", "SOLUÇÕES FISCAIS  •  AUTOMAÇÃO DE ROTINAS FISCAIS",
          Font(name=FONTE, size=14, bold=True, color="FFFFFF"))

    # título principal (4 linhas de altura + quebra de linha = nada é cortado)
    caixa("B5:O8", "Consulta | Download de XML NFS-e",
          Font(name=FONTE, size=26, bold=True, color=COR_VERDE))
    caixa("B10:O10", "Padrão Nacional  —  Portal Nacional da NFS-e / ADN",
          Font(name=FONTE, size=11, color="666666"))
    pintar("B12:O12", OURO)  # barra de destaque

    # contatos
    for i, contato in enumerate(CONTATOS):
        linha = 14 + i * 2
        caixa(f"B{linha}:O{linha}", contato, Font(name=FONTE, size=11, color="333333"))

    # cartões de estatística (título, valor, subtítulo) — fonte adaptada ao tamanho do valor
    posicoes = [("B", "E"), ("G", "J"), ("L", "O")]
    for (col_ini, col_fim), (titulo, valor, subtitulo) in zip(posicoes, cartoes_dados):
        caixa(f"{col_ini}20:{col_fim}20", titulo,
              Font(name=FONTE, size=8, bold=True, color="FFFFFF"), centro, COR_AZUL)
        tamanho_valor = 20 if len(str(valor)) <= 8 else (14 if len(str(valor)) <= 13 else 11)
        caixa(f"{col_ini}21:{col_fim}21", str(valor),
              Font(name=FONTE, size=tamanho_valor, bold=True, color=COR_AZUL), centro, AZUL_CLARO)
        caixa(f"{col_ini}22:{col_fim}22", subtitulo,
              Font(name=FONTE, size=8, italic=True, color="888888"), centro, AZUL_CLARO)

    # informações da geração (uma informação por linha, sem depender de quebra)
    caixa("B24:O24", f"Competência {competencia}  •  Gerado em {datetime.now().strftime('%d/%m/%Y %H:%M')}",
          Font(name=FONTE, size=10, bold=True, color=COR_AZUL))
    caixa("B25:O25", "Processo 100% automático, sem digitação manual",
          Font(name=FONTE, size=10, color="555555"))
    lista_cnpjs = ", ".join(sorted(cnpjs)) or "-"
    if len(cnpjs) > 12:
        raizes = ", ".join(sorted({c[:8] for c in cnpjs}))
        lista_cnpjs = f"{len(cnpjs)} CNPJs monitorados (raízes: {raizes})"
    caixa("B26:O28", f"CNPJ(s) monitorado(s): {lista_cnpjs}",
          Font(name=FONTE, size=8, color="555555"),
          Alignment(horizontal="left", vertical="top", wrap_text=True))

    # robô
    try:
        PASTA_APP.mkdir(parents=True, exist_ok=True)
        caminho_robo = desenhar_robo(PASTA_APP / "robo.png")
    except Exception:
        caminho_robo = None
    if caminho_robo:
        from openpyxl.drawing.image import Image as ImagemXL
        robo = ImagemXL(str(caminho_robo))
        robo.width, robo.height = 255, 330
        ws.add_image(robo, "P5")

    # rodapé
    pintar("A30:V31", COR_AZUL)
    caixa("B30:V31", "SOLUÇÕES FISCAIS  —  Soluções inteligentes para a sua rotina fiscal",
          Font(name=FONTE, size=11, italic=True, color="FFFFFF"))


SECOES_COLUNAS = {
    "emit": "Emitente", "prest": "Prestador", "toma": "Tomador", "interm": "Intermediário",
    "dest": "Destinatário", "serv": "Serviço", "valores": "Valores", "tribMun": "Trib. Municipal",
    "tribFed": "Trib. Federal", "piscofins": "PIS/COFINS", "totTrib": "Tot. Tributos",
    "regTrib": "Reg. Trib.", "end": "End.", "endNac": "End.", "enderNac": "End.",
    "infDPS": "DPS", "IBSCBS": "IBS/CBS", "exigSusp": "Susp.", "BM": "BM",
}
CAMPOS_COLUNAS = {
    "nNFSe": "Número NFS-e", "dhProc": "Data Processamento", "dCompet": "Competência",
    "dhEmi": "Data Emissão", "nDPS": "Número DPS", "serie": "Série DPS", "tpAmb": "Ambiente",
    "cStat": "Situação", "nDFSe": "Nº DFS-e", "verAplic": "Versão Aplic.", "tpEmis": "Tipo Emissão",
    "procEmi": "Processo Emissão", "ambGer": "Ambiente Gerador", "tpEmit": "Emitente da NFS-e",
    "xLocEmi": "Município Emissor", "cLocEmi": "Cód. Mun. Emissor", "xLocPrestacao": "Local Prestação",
    "cLocPrestacao": "Cód. Local Prestação", "cLocIncid": "Cód. Mun. Incidência",
    "xLocIncid": "Mun. Incidência", "xTribNac": "Descr. Trib. Nacional", "xTribMun": "Descr. Trib. Municipal",
    "cTribNac": "Cód. Trib. Nacional", "cTribMun": "Cód. Trib. Municipal", "cNBS": "Cód. NBS",
    "xNBS": "Descr. NBS", "xDescServ": "Descrição do Serviço", "CNPJ": "CNPJ", "CPF": "CPF",
    "NIF": "NIF", "IM": "Inscr. Municipal", "xNome": "Nome", "fone": "Telefone", "email": "E-mail",
    "xLgr": "Logradouro", "nro": "Número", "xCpl": "Complemento", "xBairro": "Bairro",
    "cMun": "Cód. Município", "CEP": "CEP", "UF": "UF", "opSimpNac": "Simples Nacional",
    "regApTribSN": "Reg. Apuração SN", "regEspTrib": "Regime Especial", "vServ": "Valor Serviço (R$)",
    "vBC": "Base de Cálculo (R$)", "pAliqAplic": "Alíquota ISSQN (%)", "vISSQN": "Valor ISSQN (R$)",
    "vLiq": "Valor Líquido (R$)", "vTotalRet": "Total Retenções (R$)", "vDescIncond": "Desc. Incond. (R$)",
    "vDescCond": "Desc. Cond. (R$)", "vDR": "Deduções/Reduções (R$)", "tribISSQN": "Trib. do ISSQN",
    "tpImunidade": "Tipo Imunidade", "tpRetISSQN": "Retenção ISSQN", "tpSusp": "Tipo Suspensão",
    "nProcesso": "Nº Processo", "tpBM": "Benefício Municipal", "vCalcBM": "Cálculo BM (R$)",
    "CST": "CST", "vBCPisCofins": "BC PIS/COFINS (R$)", "pAliqPis": "Alíq. PIS (%)",
    "pAliqCofins": "Alíq. COFINS (%)", "vPis": "Valor PIS (R$)", "vCofins": "Valor COFINS (R$)",
    "tpRetPisCofins": "Ret. PIS/COFINS", "vRetCP": "Contrib. Prev. Retida (R$)",
    "vRetIRRF": "IRRF Retido (R$)", "vRetCSLL": "CSLL Retida (R$)",
    "pTotTribFed": "% Trib. Federais", "pTotTribEst": "% Trib. Estaduais",
    "pTotTribMun": "% Trib. Municipais", "vTotTribFed": "Trib. Federais (R$)",
    "vTotTribEst": "Trib. Estaduais (R$)", "vTotTribMun": "Trib. Municipais (R$)",
    "versao": "Versão", "Id": "Id", "xInfComp": "Inf. Complementares", "chSubstda": "Chave Substituída",
}


def _titulo_coluna(caminho: str) -> str:
    especiais = {"arquivo": "Arquivo XML", "nsu_distribuicao": "NSU", "chave_acesso": "Chave de Acesso",
                 "situacao_atual": "Situação Atual", "empresa_origem": "Empresa"}
    if caminho in especiais:
        return especiais[caminho]
    partes = re.split(r"[.@]", caminho)
    folha = re.sub(r"\[\d+\]$", "", partes[-1])
    sufixo = re.search(r"\[(\d+)\]$", partes[-1])
    secoes = [SECOES_COLUNAS[p] for p in partes[:-1] if SECOES_COLUNAS.get(p)]
    nome = CAMPOS_COLUNAS.get(folha, folha)
    titulo = f"{secoes[-1]} – {nome}" if secoes else nome
    if sufixo:
        titulo += f" ({sufixo.group(1)})"
    return titulo


def aba_notas(wb, titulo, arquivos, situacoes=None, log=None, origem=None):
    from openpyxl.styles import Alignment, Font, PatternFill
    from openpyxl.utils import get_column_letter

    ws = wb.create_sheet(titulo)
    ws.sheet_view.showGridLines = False
    ws.sheet_properties.tabColor = COR_AZUL

    situacoes = situacoes or {}
    origem = origem or {}  # planilha agrupada: nome do arquivo -> pasta da empresa
    colunas = ["arquivo", "chave_acesso", "situacao_atual"]
    if origem:
        colunas.append("empresa_origem")
    linhas = []
    for arquivo in sorted(arquivos):
        if log and len(linhas) and len(linhas) % 2000 == 0:
            log(f"   lendo notas... {len(linhas)} de {len(arquivos)}")
        try:
            raiz = ET.parse(_caminho_longo(arquivo)).getroot()
        except (ET.ParseError, OSError):
            continue
        m = re.search(r"_(\d{50})\.xml$", arquivo.name)
        chave = m.group(1) if m else ""
        linha = {"arquivo": arquivo.name, "chave_acesso": chave,
                 "situacao_atual": situacoes.get(chave, "Normal")}
        if origem:
            linha["empresa_origem"] = origem.get(arquivo.name, "")
        for filho in raiz:
            _achatar(filho, "", linha)
        for coluna in linha:
            if coluna not in colunas:
                colunas.append(coluna)
        linhas.append(linha)
    linhas.sort(key=lambda l: str(l.get("infNFSe.DPS.infDPS.dhEmi", "")))

    # linha 1: descrição amigável (identidade visual da capa); linha 2: tag técnica do XML
    ws.append([_titulo_coluna(c) for c in colunas])
    ws.append(colunas)
    fundo_cabecalho = PatternFill("solid", fgColor=COR_AZUL)
    fonte_cabecalho = Font(name="Segoe UI", size=9, bold=True, color="FFFFFF")
    central = Alignment(horizontal="center", vertical="center", wrap_text=True)
    fundo_tecnico = PatternFill("solid", fgColor="EAF1FB")
    fonte_tecnica = Font(name="Segoe UI", size=7, italic=True, color="666666")
    for celula in ws[1]:
        celula.fill = fundo_cabecalho
        celula.font = fonte_cabecalho
        celula.alignment = central
    for celula in ws[2]:
        celula.fill = fundo_tecnico
        celula.font = fonte_tecnica
        celula.alignment = Alignment(horizontal="center", vertical="center")
    ws.row_dimensions[1].height = 32
    ws.row_dimensions[2].height = 12

    for linha in linhas:
        ws.append([linha.get(c) for c in colunas])
    for linha_celulas in ws.iter_rows(min_row=3):
        for celula in linha_celulas:
            if isinstance(celula.value, float):
                celula.number_format = "#,##0.00"

    # destaque na coluna Situação Atual (col 3) para canceladas/substituídas
    fonte_cancelada = Font(name="Segoe UI", size=9, bold=True, color="C62828")
    fonte_substituida = Font(name="Segoe UI", size=9, bold=True, color="B26A00")
    for linha_num in range(3, ws.max_row + 1):
        celula = ws.cell(row=linha_num, column=3)
        if celula.value == "Cancelada":
            celula.font = fonte_cancelada
        elif celula.value == "Substituída":
            celula.font = fonte_substituida

    larguras_especiais = {"arquivo": 34, "chave_acesso": 52, "situacao_atual": 14,
                          "empresa_origem": 42}
    for indice, coluna in enumerate(colunas, start=1):
        if coluna in larguras_especiais:
            largura = larguras_especiais[coluna]
        elif coluna.endswith("xDescServ") or coluna.endswith("xInfComp"):
            largura = 45
        else:
            largura = max(12, min(26, len(_titulo_coluna(coluna)) + 4))
        ws.column_dimensions[get_column_letter(indice)].width = largura

    ws.freeze_panes = "D3"
    if linhas:
        ws.auto_filter.ref = f"A2:{get_column_letter(len(colunas))}{ws.max_row}"
    return linhas


# ----------------------------------------------------------------------------
# DANFSe v2.0 — modelo oficial conforme NT 008/2026 (Anexo I)
# A API oficial foi descontinuada em 03/08/2026; a NT determina que os sistemas
# gerem o DANFSe seguindo exatamente o modelo, posições e fontes especificados.
# ----------------------------------------------------------------------------

CM = 28.3465  # pontos por centímetro

UF_POR_CODIGO = {
    "11": "RO", "12": "AC", "13": "AM", "14": "RR", "15": "PA", "16": "AP", "17": "TO",
    "21": "MA", "22": "PI", "23": "CE", "24": "RN", "25": "PB", "26": "PE", "27": "AL",
    "28": "SE", "29": "BA", "31": "MG", "32": "ES", "33": "RJ", "35": "SP",
    "41": "PR", "42": "SC", "43": "RS", "50": "MS", "51": "MT", "52": "GO", "53": "DF",
}
DESC_TPEMIT = {"1": "Prestador", "2": "Tomador", "3": "Intermediário"}
DESC_CSTAT = {"100": "NFS-e Gerada", "101": "NFS-e Cancelada", "102": "NFS-e Substituída",
              "107": "NFS-e do MEI Gerada"}
DESC_SIMPNAC = {"1": "Não Optante", "2": "Optante - Microempreendedor Individual (MEI)",
                "3": "Optante - Microempresa ou Empresa de Pequeno Porte (ME/EPP)"}
DESC_REGAP = {"1": "Regime de apuração dos tributos federais e municipal pelo Simples Nacional",
              "2": "Regime de apuração dos tributos federais pelo Simples Nacional",
              "3": "Regime de apuração dos tributos federais e municipal fora do Simples Nacional"}
DESC_TRIBISSQN = {"1": "Operação Tributável", "2": "Exportação de serviço",
                  "3": "Não Incidência", "4": "Imunidade"}
DESC_REGESP = {"0": "Nenhum", "1": "Ato Cooperado", "2": "Estimativa", "3": "Microempresa Municipal",
               "4": "Notário ou Registrador", "5": "Profissional Autônomo", "6": "Sociedade de Profissionais"}
DESC_RETISSQN = {"1": "Não Retido", "2": "Retido pelo Tomador", "3": "Retido pelo Intermediário"}
DESC_RETPIS = {"1": "PIS/COFINS Retido", "2": "PIS/COFINS Não Retido"}
DESC_AMBGER = {"1": "Prefeitura", "2": "Ambiente Nacional"}
DESC_TPAMB = {"1": "Produção", "2": "Homologação"}

_FONTES = {}


def _fontes_danfse():
    """Registra Arial e Microsoft Sans Serif (fontes exigidas pela NT); usa Helvetica se faltarem."""
    if _FONTES:
        return _FONTES
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    fontes = {"negrito": "Helvetica-Bold", "normal": "Helvetica", "conteudo": "Helvetica"}
    janelas = Path("C:/Windows/Fonts")
    for chave, arquivo, nome in (("negrito", "arialbd.ttf", "ArialNegrito"),
                                 ("normal", "arial.ttf", "ArialNormal"),
                                 ("conteudo", "micross.ttf", "MSSansSerif")):
        try:
            pdfmetrics.registerFont(TTFont(nome, str(janelas / arquivo)))
            fontes[chave] = nome
        except Exception:
            pass
    _FONTES.update(fontes)
    return _FONTES


def _filho(elemento, nome):
    if elemento is None:
        return None
    return next((f for f in elemento if _local(f.tag) == nome), None)


def _campo(pai, nome):
    if pai is None:
        return ""
    filho = _achar(pai, nome)
    return (filho.text or "").strip() if filho is not None else ""


def _fmt_doc(documento):
    if len(documento) == 14:
        return f"{documento[:2]}.{documento[2:5]}.{documento[5:8]}/{documento[8:12]}-{documento[12:]}"
    if len(documento) == 11:
        return f"{documento[:3]}.{documento[3:6]}.{documento[6:9]}-{documento[9:]}"
    return documento


def _fmt_moeda(valor):
    if not valor:
        return "-"
    try:
        texto = f"{float(valor):,.2f}".replace(",", "@").replace(".", ",").replace("@", ".")
        return f"R$ {texto}"
    except ValueError:
        return valor


def _fmt_pct(valor):
    if not valor:
        return "-"
    try:
        return f"{float(valor):.2f}".replace(".", ",") + " %"
    except ValueError:
        return valor


def _fmt_data(iso):
    if not iso:
        return "-"
    try:
        return datetime.fromisoformat(iso[:10]).strftime("%d/%m/%Y")
    except ValueError:
        return iso


def _fmt_datahora(iso):
    if not iso:
        return "-"
    try:
        return datetime.fromisoformat(iso.replace("Z", "")).strftime("%d/%m/%Y %H:%M:%S")
    except ValueError:
        return iso[:19]


def _fmt_ctrib(codigo):
    if len(codigo) == 6:
        return f"{codigo[:2]}.{codigo[2:4]}.{codigo[4:]}"
    return codigo or "-"


def _uf_do_codigo(cmun):
    return UF_POR_CODIGO.get(cmun[:2], "") if cmun else ""


def gerar_pdf_nota(arquivo_xml: Path, destino_pdf: Path, marca_dagua: str = None):
    """Gera o DANFSe v2.0 no modelo oficial do Anexo I da NT 008/2026."""
    import base64
    import io

    import qrcode
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.utils import ImageReader, simpleSplit
    from reportlab.pdfgen import canvas as rl_canvas

    fontes = _fontes_danfse()
    NEGRITO, NORMAL, TEXTO = fontes["negrito"], fontes["normal"], fontes["conteudo"]

    raiz = ET.parse(_caminho_longo(arquivo_xml)).getroot()
    inf_nfse = _achar(raiz, "infNFSe")
    dps = _filho(inf_nfse, "DPS")
    inf_dps = _achar(dps, "infDPS") if dps is not None else None
    emit = _filho(inf_nfse, "emit")
    valores_nfse = _filho(inf_nfse, "valores")
    prest = _filho(inf_dps, "prest")
    toma = _filho(inf_dps, "toma")
    interm = _filho(inf_dps, "interm")
    serv = _filho(inf_dps, "serv")
    valores_dps = _filho(inf_dps, "valores")
    trib_mun = _achar(valores_dps, "tribMun") if valores_dps is not None else None
    trib_fed = _achar(valores_dps, "tribFed") if valores_dps is not None else None
    piscofins = _achar(trib_fed, "piscofins") if trib_fed is not None else None

    m = re.search(r"_(\d{50})\.xml$", arquivo_xml.name)
    chave = m.group(1) if m else _campo(inf_nfse, "Id").replace("NFS", "")

    # nomes de município conhecidos no próprio XML (leiaute antigo não traz o nome do município do tomador)
    nomes_municipio = {}
    for codigo, nome in ((_campo(emit, "cMun"), _campo(inf_nfse, "xLocEmi")),
                         (_campo(inf_nfse, "cLocIncid"), _campo(inf_nfse, "xLocIncid")),
                         (_campo(inf_dps, "cLocEmi") if inf_dps is not None else "", _campo(inf_nfse, "xLocEmi"))):
        if codigo and nome:
            nomes_municipio[codigo] = nome

    largura, altura = A4
    c = rl_canvas.Canvas(str(destino_pdf), pagesize=A4)
    CINZA_5PCT = 0.95

    def x_pt(cm_):
        return cm_ * CM

    def y_pt(cm_):
        return altura - cm_ * CM

    def celula(esq, sup, larg, alt, sombra=False):
        c.setLineWidth(0.5)
        c.setStrokeColorRGB(0, 0, 0)
        if sombra:
            c.setFillGray(CINZA_5PCT)
            c.rect(x_pt(esq), y_pt(sup + alt), larg * CM, alt * CM, fill=1)
            c.setFillGray(0)
        else:
            c.rect(x_pt(esq), y_pt(sup + alt), larg * CM, alt * CM)

    def rotulo(esq, sup, texto, tamanho=6, caps=False):
        c.setFont(NEGRITO, tamanho)
        c.setFillGray(0)
        c.drawString(x_pt(esq + 0.06), y_pt(sup + 0.09 + tamanho / 72 * 2.54), texto.upper() if caps else texto)

    def conteudo(esq, sup, texto, desloc=0.34, tamanho=7, larg_max=None):
        c.setFont(TEXTO, tamanho)
        c.setFillGray(0)
        texto = texto if texto else "-"
        if larg_max:
            linhas = simpleSplit(texto, TEXTO, tamanho, larg_max * CM)
            texto = (linhas[0][: len(linhas[0]) - 3] + "...") if len(linhas) > 1 else (linhas[0] if linhas else "-")
        c.drawString(x_pt(esq + 0.06), y_pt(sup + desloc + 0.18), texto)

    def campo(esq, sup, larg, alt, titulo, valor, caps=False, tam_rotulo=6):
        celula(esq, sup, larg, alt)
        rotulo(esq, sup, titulo, tam_rotulo, caps)
        conteudo(esq, sup, valor, desloc=alt - 0.29, larg_max=larg - 0.12)

    def titulo_bloco(esq, sup, larg, alt, texto):
        celula(esq, sup, larg, alt, sombra=True)
        c.setFont(NEGRITO, 7)
        c.drawString(x_pt(esq + 0.06), y_pt(sup + alt / 2 + 0.11), texto)

    def linha_unica_bloco(sup, alt, texto):
        celula(0.30, sup, 20.40, alt)
        c.setFont(NEGRITO, 7)
        c.drawString(x_pt(0.36), y_pt(sup + alt / 2 + 0.11), texto)

    try:
        from municipios_ibge import MUNICIPIOS_IBGE
    except ImportError:
        MUNICIPIOS_IBGE = {}

    def municipio_uf(elemento):
        cidade_ext = _campo(elemento, "xCidade")
        if cidade_ext:
            return cidade_ext
        cmun = _campo(elemento, "cMun")
        nome_uf = MUNICIPIOS_IBGE.get(cmun)
        if nome_uf:
            return nome_uf
        nome = nomes_municipio.get(cmun, "")
        return f"{nome} / {_uf_do_codigo(cmun)}" if nome else "-"

    def ibge_cep(elemento):
        cmun = _campo(elemento, "cMun")
        cep = _campo(elemento, "CEP") or _campo(elemento, "cEndPost")
        if not cmun and not cep:
            return "-"
        cep_formatado = f"{cep[:2]}.{cep[2:5]}-{cep[5:]}" if len(cep) == 8 else cep
        return f"{cmun or '-'} / {cep_formatado or '-'}"

    def endereco(elemento):
        partes = [_campo(elemento, "xLgr"), _campo(elemento, "nro"),
                  _campo(elemento, "xCpl"), _campo(elemento, "xBairro")]
        return ", ".join(p for p in partes if p)

    # ------------------------------------------------------------------ página
    c.setLineWidth(1)
    c.rect(x_pt(0.15), y_pt(29.55), 20.70 * CM, 29.40 * CM)

    # ---------------------------------------------------------------- cabeçalho
    celula(0.30, 0.30, 20.40, 1.16, sombra=True)
    try:
        from logo_nfse import LOGO_NFSE_B64
        imagem_logo = ImageReader(io.BytesIO(base64.b64decode(LOGO_NFSE_B64)))
        c.drawImage(imagem_logo, x_pt(0.49), y_pt(0.44 + 0.85), 4.00 * CM, 0.85 * CM,
                    preserveAspectRatio=True, anchor="w", mask="auto")
    except Exception:
        c.setFont(NEGRITO, 11)
        c.drawString(x_pt(0.49), y_pt(0.95), "NFS-e")
    c.setFont(NEGRITO, 9)
    tp_amb = _campo(inf_dps, "tpAmb") if inf_dps is not None else ""
    c.drawCentredString(x_pt(5.41 + 10.19 / 2), y_pt(0.72), "DANFSe v2.0")
    c.drawCentredString(x_pt(5.41 + 10.19 / 2), y_pt(1.06), "Documento Auxiliar da NFS-e")
    if tp_amb == "2":
        c.setFillColorRGB(1, 0, 0)
        c.drawCentredString(x_pt(5.41 + 10.19 / 2), y_pt(1.40), "NFS-e SEM VALIDADE JURÍDICA")
        c.setFillGray(0)
    c.setFont(TEXTO, 8)
    municipio_emitente = _campo(inf_nfse, "xLocEmi")
    uf_emitente = _campo(emit, "UF") or _uf_do_codigo(_campo(emit, "cMun"))
    c.drawString(x_pt(15.62), y_pt(0.62), f"Município: {municipio_emitente} - {uf_emitente}"[:44])
    c.setFont(TEXTO, 6)
    c.drawString(x_pt(15.62), y_pt(1.06), f"Ambiente Gerador: {DESC_AMBGER.get(_campo(inf_nfse, 'ambGer'), '-')}")
    c.drawString(x_pt(15.62), y_pt(1.30), f"Tipo de Ambiente: {DESC_TPAMB.get(tp_amb, '-')}")

    # --------------------------------------------------------- dados da NFS-e
    campo(0.30, 1.48, 15.30, 0.77, "CHAVE DE ACESSO DA NFS-E", chave, tam_rotulo=7)
    campo(0.30, 2.27, 5.09, 0.67, "NÚMERO DA NFS-e", _campo(inf_nfse, "nNFSe"), tam_rotulo=7)
    campo(5.41, 2.27, 5.09, 0.67, "COMPETÊNCIA DA NFS-e",
          _fmt_data(_campo(inf_dps, "dCompet") if inf_dps is not None else ""), tam_rotulo=7)
    campo(10.51, 2.27, 5.09, 0.67, "DATA E HORA DA EMISSÃO DA NFS-E",
          _fmt_datahora(_campo(inf_nfse, "dhProc")), tam_rotulo=7)
    campo(0.30, 2.96, 5.09, 0.67, "NÚMERO DA DPS",
          _campo(inf_dps, "nDPS") if inf_dps is not None else "", tam_rotulo=7)
    campo(5.41, 2.96, 5.09, 0.67, "SÉRIE DA DPS",
          _campo(inf_dps, "serie") if inf_dps is not None else "", tam_rotulo=7)
    campo(10.51, 2.96, 5.09, 0.67, "DATA E HORA DA EMISSÃO DA DPS",
          _fmt_datahora(_campo(inf_dps, "dhEmi") if inf_dps is not None else ""), tam_rotulo=7)
    celula(0.30, 3.65, 5.09, 0.67, sombra=True)
    rotulo(0.30, 3.65, "EMITENTE DA NFS-E", 7)
    conteudo(0.30, 3.65, DESC_TPEMIT.get(_campo(inf_dps, "tpEmit") if inf_dps is not None else "", "-"),
             desloc=0.38)
    campo(5.41, 3.65, 5.09, 0.67, "SITUAÇÃO DA NFS-E",
          DESC_CSTAT.get(_campo(inf_nfse, "cStat"), _campo(inf_nfse, "cStat")), tam_rotulo=7)
    campo(10.51, 3.65, 5.09, 0.67, "FINALIDADE",
          _campo(inf_dps, "finNFSe") if inf_dps is not None else "", tam_rotulo=7)

    # QR Code (posição e URL oficiais)
    imagem_qr = qrcode.make(f"https://www.nfse.gov.br/ConsultaPublica/?tpc=1&chave={chave}")
    memoria = io.BytesIO()
    try:
        imagem_qr.get_image().save(memoria, "PNG")
    except AttributeError:
        imagem_qr.save(memoria, "PNG")
    memoria.seek(0)
    c.drawImage(ImageReader(memoria), x_pt(17.48), y_pt(1.67 + 1.52), 1.52 * CM, 1.52 * CM)
    c.setFont(TEXTO, 6)
    aviso_qr = ("A autenticidade desta NFS-e pode ser verificada pela leitura deste código QR "
                "ou pela consulta da chave de acesso no portal nacional da NFS-e")
    for i, linha in enumerate(simpleSplit(aviso_qr, TEXTO, 6, 4.72 * CM)[:3]):
        c.drawString(x_pt(15.80), y_pt(3.50 + i * 0.22), linha)

    # ---------------------------------------------------------------- prestador
    titulo_bloco(0.30, 4.34, 5.09, 0.63, "PRESTADOR / FORNECEDOR")
    doc_prest = _campo(prest, "CNPJ") or _campo(prest, "CPF") or _campo(prest, "NIF")
    campo(5.41, 4.34, 5.09, 0.63, "CNPJ / CPF / NIF", _fmt_doc(doc_prest))
    campo(10.51, 4.34, 5.09, 0.63, "Indicador Municipal (Inscrição)", _campo(prest, "IM"))
    campo(15.62, 4.34, 5.09, 0.63, "Telefone", _campo(prest, "fone") or _campo(emit, "fone"))
    campo(0.30, 4.98, 10.19, 0.63, "Nome / Nome Empresarial",
          _campo(prest, "xNome") or _campo(emit, "xNome"))
    ender_emit = _filho(emit, "enderNac") or emit
    campo(10.51, 4.98, 5.09, 0.63, "Município / Sigla UF", f"{municipio_emitente} / {uf_emitente}")
    campo(15.62, 4.98, 5.09, 0.63, "Código IBGE / CEP", ibge_cep(ender_emit))
    campo(0.30, 5.62, 10.19, 0.63, "Endereço", endereco(ender_emit))
    campo(10.51, 5.62, 10.19, 0.63, "E-mail", _campo(prest, "email") or _campo(emit, "email"))
    reg_trib = _achar(prest, "regTrib") if prest is not None else None
    campo(0.30, 6.28, 5.09, 0.63, "Simples Nacional na Data de Competência",
          DESC_SIMPNAC.get(_campo(reg_trib, "opSimpNac"), "-"))
    campo(10.51, 6.28, 10.19, 0.63, "Regime de Apuração Tributária pelo SN",
          DESC_REGAP.get(_campo(reg_trib, "regApTribSN"), "-"))

    # ------------------------------------------------------------------ tomador
    if toma is not None:
        titulo_bloco(0.30, 6.92, 5.09, 0.63, "TOMADOR / ADQUIRENTE")
        doc_toma = _campo(toma, "CNPJ") or _campo(toma, "CPF") or _campo(toma, "NIF")
        campo(5.41, 6.92, 5.09, 0.63, "CNPJ / CPF / NIF", _fmt_doc(doc_toma))
        campo(10.51, 6.92, 5.09, 0.63, "Indicador Municipal (Inscrição)", _campo(toma, "IM"))
        campo(15.62, 6.92, 5.09, 0.63, "Telefone", _campo(toma, "fone"))
        campo(0.30, 7.56, 10.19, 0.63, "Nome / Nome Empresarial", _campo(toma, "xNome"))
        ender_toma = _achar(toma, "endNac") or _achar(toma, "end") or toma
        campo(10.51, 7.56, 5.09, 0.63, "Município / Sigla UF", municipio_uf(ender_toma))
        campo(15.62, 7.56, 5.09, 0.63, "Código IBGE / CEP", ibge_cep(ender_toma))
        campo(0.30, 8.22, 10.19, 0.63, "Endereço", endereco(_achar(toma, "end") or toma))
        campo(10.51, 8.22, 10.19, 0.63, "E-mail", _campo(toma, "email"))
    else:
        linha_unica_bloco(6.92, 1.94, "TOMADOR/ADQUIRENTE DA OPERAÇÃO NÃO IDENTIFICADO NA NFS-e")

    # ------------------------------------------------------------- destinatário
    ibscbs = _achar(inf_dps, "IBSCBS") if inf_dps is not None else None
    dest = _achar(ibscbs, "dest") if ibscbs is not None else None
    if dest is not None:
        titulo_bloco(0.30, 8.86, 5.09, 0.63, "DESTINATÁRIO DA OPERAÇÃO")
        campo(5.41, 8.86, 5.09, 0.63, "CNPJ / CPF / NIF",
              _fmt_doc(_campo(dest, "CNPJ") or _campo(dest, "CPF") or _campo(dest, "NIF")))
        campo(15.62, 8.86, 5.09, 0.63, "Telefone", _campo(dest, "fone"))
        campo(0.30, 9.50, 10.19, 0.63, "Nome / Nome Empresarial", _campo(dest, "xNome"))
        ender_dest = _achar(dest, "end") or dest
        campo(10.51, 9.50, 5.09, 0.63, "Município / Sigla UF", municipio_uf(ender_dest))
        campo(15.62, 9.50, 5.09, 0.63, "Código IBGE / CEP", ibge_cep(ender_dest))
        campo(0.30, 10.16, 10.19, 0.63, "Endereço", endereco(ender_dest))
        campo(10.51, 10.16, 10.19, 0.63, "E-mail", _campo(dest, "email"))
    elif toma is not None:
        linha_unica_bloco(8.86, 1.94, "O DESTINATÁRIO É O PRÓPRIO TOMADOR/ADQUIRENTE DA OPERAÇÃO")
    else:
        linha_unica_bloco(8.86, 1.94, "DESTINATÁRIO DA OPERAÇÃO NÃO IDENTIFICADO NA NFS-e")

    # ------------------------------------------------------------- intermediário
    if interm is not None:
        titulo_bloco(0.30, 10.80, 5.09, 0.63, "INTERMEDIÁRIO DA OPERAÇÃO")
        campo(5.41, 10.80, 5.09, 0.63, "CNPJ / CPF / NIF",
              _fmt_doc(_campo(interm, "CNPJ") or _campo(interm, "CPF") or _campo(interm, "NIF")))
        campo(10.51, 10.80, 5.09, 0.63, "Indicador Municipal (Inscrição)", _campo(interm, "IM"))
        campo(15.62, 10.80, 5.09, 0.63, "Telefone", _campo(interm, "fone"))
        campo(0.30, 11.44, 10.19, 0.63, "Nome / Nome Empresarial", _campo(interm, "xNome"))
        ender_interm = _achar(interm, "endNac") or _achar(interm, "end") or interm
        campo(10.51, 11.44, 5.09, 0.63, "Município / Sigla UF", municipio_uf(ender_interm))
        campo(15.62, 11.44, 5.09, 0.63, "Código IBGE / CEP", ibge_cep(ender_interm))
        campo(0.30, 12.09, 10.19, 0.63, "Endereço", endereco(_achar(interm, "end") or interm))
        campo(10.51, 12.09, 10.19, 0.63, "E-mail", _campo(interm, "email"))
    else:
        linha_unica_bloco(10.80, 1.94, "INTERMEDIÁRIO DA OPERAÇÃO NÃO IDENTIFICADO NA NFS-e")

    # ---------------------------------------------------------- serviço prestado
    titulo_bloco(0.30, 12.74, 5.09, 0.63, "SERVIÇO PRESTADO")
    c_trib_nac = _campo(serv, "cTribNac")
    c_trib_mun = _campo(serv, "cTribMun")
    codigo_trib = _fmt_ctrib(c_trib_nac) + (f" / {c_trib_mun}" if c_trib_mun else "")
    campo(5.41, 12.74, 5.09, 0.63, "Código de Tributação Nacional / Municipal", codigo_trib)
    campo(10.51, 12.74, 5.09, 0.63, "Código da NBS", _campo(serv, "cNBS"))
    local_prest = _campo(inf_nfse, "xLocPrestacao")
    c_loc_prest = _campo(serv, "cLocPrestacao")
    pais = _campo(serv, "cPaisPrestacao") or "BR"
    campo(15.62, 12.74, 5.09, 0.63, "Local da Prestação / Sigla UF / País",
          f"{local_prest} / {_uf_do_codigo(c_loc_prest)} / {pais}" if local_prest else "-")

    celula(0.30, 13.39, 20.40, 0.38)
    conteudo(0.30, 13.39, (_campo(inf_nfse, "xTribMun") or _campo(inf_nfse, "xTribNac")),
             desloc=0.09, larg_max=20.28)
    celula(0.30, 13.79, 20.40, 2.39)
    rotulo(0.30, 13.79, "Descrição do Serviço")
    c.setFont(TEXTO, 7)
    descricao = _campo(serv, "xDescServ") or "-"
    linhas_descricao = simpleSplit(descricao, TEXTO, 7, 20.20 * CM)
    for i, linha in enumerate(linhas_descricao[:7]):
        if i == 6 and len(linhas_descricao) > 7:
            linha = linha[: max(0, len(linha) - 3)] + "..."
        c.drawString(x_pt(0.36), y_pt(14.32 + i * 0.27), linha)

    # ------------------------------------------------- tributação municipal ISSQN
    titulo_bloco(0.30, 16.18, 5.09, 0.63, "TRIBUTAÇÃO MUNICIPAL (ISSQN)")
    campo(5.41, 16.18, 5.09, 0.63, "Tipo de Tributação do ISSQN",
          DESC_TRIBISSQN.get(_campo(trib_mun, "tribISSQN"), "-"))
    loc_incid = _campo(inf_nfse, "xLocIncid")
    campo(10.51, 16.18, 10.19, 0.63, "Município / Sigla UF / País de Incidência do ISSQN",
          f"{loc_incid} / {_uf_do_codigo(_campo(inf_nfse, 'cLocIncid'))} / BR" if loc_incid else "-")
    exig_susp = _achar(trib_mun, "exigSusp") if trib_mun is not None else None
    campo(0.30, 16.83, 5.09, 0.63, "Regime Especial de Tributação do ISSQN",
          DESC_REGESP.get(_campo(reg_trib, "regEspTrib"), "-"))
    campo(5.41, 16.83, 5.09, 0.63, "Tipo de Imunidade do ISSQN", _campo(trib_mun, "tpImunidade") or "-")
    campo(10.51, 16.83, 5.09, 0.63, "Suspensão da Exigibilidade do ISSQN", _campo(exig_susp, "tpSusp"))
    campo(15.62, 16.83, 5.09, 0.63, "Número Processo Suspensão", _campo(exig_susp, "nProcesso"))
    campo(0.30, 17.48, 5.09, 0.63, "Benefício Municipal", _campo(valores_nfse, "tpBM"))
    campo(5.41, 17.48, 5.09, 0.63, "Cálculo do BM", _fmt_moeda(_campo(valores_nfse, "vCalcBM")))
    campo(10.51, 17.48, 5.09, 0.63, "Total Deduções/Reduções",
          _fmt_moeda(_campo(valores_dps, "vDR") or _campo(valores_nfse, "vCalcDR")))
    desconto_incond = _campo(valores_dps, "vDescIncond")
    campo(15.62, 17.48, 5.09, 0.63, "Desconto Incondicionado", _fmt_moeda(desconto_incond))
    campo(0.30, 18.12, 5.09, 0.63, "BC ISSQN", _fmt_moeda(_campo(valores_nfse, "vBC")))
    campo(5.41, 18.12, 5.09, 0.63, "Alíquota Aplicada", _fmt_pct(_campo(valores_nfse, "pAliqAplic")))
    campo(10.51, 18.12, 5.09, 0.63, "Retenção do ISSQN",
          DESC_RETISSQN.get(_campo(trib_mun, "tpRetISSQN"), "-"))
    campo(15.62, 18.12, 5.09, 0.63, "ISSQN Apurado", _fmt_moeda(_campo(valores_nfse, "vISSQN")))

    # --------------------------------------------------------- tributação federal
    titulo_bloco(0.30, 18.77, 5.09, 0.63, "TRIBUTAÇÃO FEDERAL (EXCETO CBS)")
    campo(5.41, 18.77, 5.09, 0.63, "IRRF", _fmt_moeda(_campo(trib_fed, "vRetIRRF")))
    campo(10.51, 18.77, 5.09, 0.63, "Contribuição Previdenciária - Retida",
          _fmt_moeda(_campo(trib_fed, "vRetCP")))
    tp_ret_pis = _campo(piscofins, "tpRetPisCofins")
    v_csll = _campo(trib_fed, "vRetCSLL")
    v_pis = _campo(piscofins, "vPis")
    v_cofins = _campo(piscofins, "vCofins")
    if tp_ret_pis == "1":
        soma_retida = sum(float(v) for v in (v_csll, v_pis, v_cofins) if v)
        contrib_retidas = _fmt_moeda(f"{soma_retida:.2f}") if soma_retida else _fmt_moeda(v_csll)
        pis_proprio, cofins_proprio = _fmt_moeda("0.00"), _fmt_moeda("0.00")
    else:
        contrib_retidas = _fmt_moeda(v_csll)
        pis_proprio, cofins_proprio = _fmt_moeda(v_pis), _fmt_moeda(v_cofins)
    campo(15.62, 18.77, 5.09, 0.63, "Contribuições Sociais - Retidas", contrib_retidas)
    campo(0.30, 19.42, 5.09, 0.63, "PIS - Débito Apuração Própria", pis_proprio)
    campo(5.41, 19.42, 5.09, 0.63, "COFINS - Débito Apuração Própria", cofins_proprio)
    campo(10.51, 19.42, 10.19, 0.63, "Descrição Contrib. Sociais - Retidas",
          DESC_RETPIS.get(tp_ret_pis, "-"))

    # ------------------------------------------------------------ tributação IBS/CBS
    valores_ibs = _achar(ibscbs, "valores") if ibscbs is not None else None
    titulo_bloco(0.30, 20.07, 5.09, 0.63, "TRIBUTAÇÃO IBS / CBS")
    cst = _campo(valores_ibs, "CST")
    campo(5.41, 20.07, 5.09, 0.63, "CST / cClassTrib",
          f"{cst} / {_campo(valores_ibs, 'cClassTrib')}" if cst else "-")
    campo(10.51, 20.07, 10.19, 0.63,
          "Indicador de Operação / Código IBGE Incidência / Município Incidência / Sigla UF", "-")
    campo(0.30, 20.71, 5.09, 0.63, "Exclusões e Reduções da Base de Cálculo", "-")
    campo(5.41, 20.71, 5.09, 0.63, "Base de Cálculo Após Exclusões e Reduções",
          _fmt_moeda(_campo(valores_ibs, "vBC")))
    campo(10.51, 20.71, 5.09, 0.63, "Red. Alíquota IBS / Red. Alíquota CBS", "-")
    campo(15.62, 20.71, 5.09, 0.63, "Alíquota - IBS UF / IBS Mun", "-")
    campo(0.30, 21.36, 5.09, 0.63, "Alíq. Efetiva Municipal - IBS", "-")
    campo(5.41, 21.36, 5.09, 0.63, "Valor Apurado Municipal - IBS", "-")
    campo(10.51, 21.36, 5.09, 0.63, "Alíq. Efetiva Estadual - IBS", "-")
    campo(15.62, 21.36, 5.09, 0.63, "Valor Apurado Estadual - IBS", "-")
    v_ibs_tot = _campo(ibscbs, "vIBSTot") if ibscbs is not None else ""
    v_cbs_tot = _campo(ibscbs, "vCBS") if ibscbs is not None else ""
    campo(0.30, 22.01, 5.09, 0.63, "Valor Total Apurado - IBS", _fmt_moeda(v_ibs_tot))
    campo(5.41, 22.01, 5.09, 0.63, "Alíquota - CBS", "-")
    campo(10.51, 22.01, 5.09, 0.63, "Alíquota Efetiva - CBS", "-")
    campo(15.62, 22.01, 5.09, 0.63, "Valor Total Apurado - CBS", _fmt_moeda(v_cbs_tot))

    # ------------------------------------------------------------- valor total
    titulo_bloco(0.30, 22.65, 5.09, 0.67, "VALOR TOTAL DA NFS-E")
    campo(5.41, 22.65, 5.09, 0.67, "VALOR DA OPERAÇÃO / SERVIÇO",
          _fmt_moeda(_campo(valores_dps, "vServ")), tam_rotulo=7)
    campo(10.51, 22.65, 5.09, 0.67, "Desconto Incondicionado", _fmt_moeda(desconto_incond))
    campo(15.62, 22.65, 5.09, 0.67, "Desconto Condicionado",
          _fmt_moeda(_campo(valores_dps, "vDescCond")))
    campo(0.30, 23.34, 5.09, 0.67, "Total das Retenções (ISSQN / Federais)",
          _fmt_moeda(_campo(valores_nfse, "vTotalRet")))
    campo(5.41, 23.34, 5.09, 0.67, "VALOR LÍQUIDO DA NFS-e",
          _fmt_moeda(_campo(valores_nfse, "vLiq")), tam_rotulo=7)
    total_ibs_cbs = ""
    if v_ibs_tot or v_cbs_tot:
        total_ibs_cbs = f"{float(v_ibs_tot or 0) + float(v_cbs_tot or 0):.2f}"
    campo(10.51, 23.34, 5.09, 0.67, "Total do IBS/CBS", _fmt_moeda(total_ibs_cbs))
    celula(15.62, 23.34, 5.09, 0.67, sombra=True)
    rotulo(15.62, 23.34, "VALOR LÍQUIDO DA NFS-e + IBS/CBS", 7)
    conteudo(15.62, 23.34, _fmt_moeda(_campo(ibscbs, "vTotNF") if ibscbs is not None else ""), desloc=0.38)

    # ------------------------------------------------- informações complementares
    celula(0.30, 24.02, 20.40, 4.08)
    rotulo(0.30, 24.02, "INFORMAÇÕES COMPLEMENTARES", 7, caps=True)
    partes_info = []
    info_compl = _achar(inf_dps, "infoCompl") if inf_dps is not None else None
    for prefixo, valor in (("Inf. Cont.: ", _campo(info_compl, "xInfComp")),
                           ("NFS-e Subst.: ", _campo(inf_dps, "chSubstda") if inf_dps is not None else ""),
                           ("Doc. Ref.: ", _campo(info_compl, "docRef")),
                           ("Cod. Obra: ", _campo(inf_dps, "cObra") if inf_dps is not None else ""),
                           ("Insc. Imob.: ", _campo(inf_dps, "inscImobFisc") if inf_dps is not None else "")):
        if valor:
            partes_info.append(prefixo + valor)
    tot_trib = _achar(valores_dps, "totTrib") if valores_dps is not None else None
    pct_fed = _campo(tot_trib, "pTotTribFed")
    pct_est = _campo(tot_trib, "pTotTribEst")
    pct_mun = _campo(tot_trib, "pTotTribMun")
    v_fed = _campo(tot_trib, "vTotTribFed")
    if pct_fed or v_fed:
        federais = _fmt_pct(pct_fed) if pct_fed else _fmt_moeda(v_fed)
        estaduais = _fmt_pct(pct_est) if pct_fed else _fmt_moeda(_campo(tot_trib, "vTotTribEst"))
        municipais = _fmt_pct(pct_mun) if pct_fed else _fmt_moeda(_campo(tot_trib, "vTotTribMun"))
    else:
        federais = estaduais = municipais = "-"
    partes_info.append("Totais Aproximados dos Tributos cfe. Lei nº12.741/2012: "
                       f"Federais: {federais}; Estaduais: {estaduais}; Municipais: {municipais};")
    texto_info = " | ".join(partes_info)
    c.setFont(TEXTO, 7)
    for i, linha in enumerate(simpleSplit(texto_info, TEXTO, 7, 20.20 * CM)[:14]):
        c.drawString(x_pt(0.36), y_pt(24.60 + i * 0.25), linha)

    # ------------------------------------------------------------------- canhoto
    celula(0.30, 28.10, 5.09, 0.67)
    rotulo(0.30, 28.10, "DATA CIENTIFICAÇÃO:", 6)
    celula(5.41, 28.10, 5.09, 0.67)
    rotulo(5.41, 28.10, "IDENTIFICAÇÃO E ASSINATURA", 6)
    campo(10.51, 28.10, 10.19, 0.67, "Nº NFS-e / CHAVE NFS-e",
          f"{_campo(inf_nfse, 'nNFSe')} / {chave}")

    # ----------------------------------------------------- marca d'água (se houver)
    if marca_dagua:
        c.saveState()
        c.setFont(fontes["normal"], 90)
        c.setFillGray(0.65)
        c.translate(largura / 2, altura / 2)
        c.rotate(45)
        c.drawCentredString(0, 0, marca_dagua)
        c.restoreState()

    c.showPage()
    c.save()


# ----------------------------------------------------------------------------
# Organização por período (Originais\Serviços Tomados\...) e planilha
# ----------------------------------------------------------------------------

def _caminho_longo(caminho: Path) -> str:
    """Prefixo \\\\?\\ do Windows para aceitar caminhos com mais de 260 caracteres."""
    texto = str(Path(caminho).resolve())
    if os.name == "nt" and not texto.startswith("\\\\?\\"):
        return "\\\\?\\" + texto
    return texto


def _nome_pdf_nota(registro: dict, tipo: str) -> str:
    numero = registro.get("numero") or "s-n"
    if tipo == "tomados":
        razao = registro.get("prestador") or registro.get("prest") or "SEM PRESTADOR"
    else:
        razao = registro.get("tomador") or registro.get("toma") or "SEM TOMADOR"
    razao = re.sub(r'[\\/:*?"<>|]', "", razao).strip()
    return f"{numero} - {razao}"[:110].rstrip() + ".pdf"


def organizar_periodos(pasta_geral: Path, log, gerar_pdfs: bool = True):
    """Distribui as notas em Serviços Tomados e Serviços Prestados, por
    ANO\\MÊS de competência, com XML e PDF (Número da Nota - Razão Social).
    Com gerar_pdfs=False apenas os XMLs são distribuídos — muito mais rápido
    em bases grandes (a geração de PDF é o passo lento do processo)."""
    completo = pasta_completa(pasta_geral)
    registros = atualizar_indice(pasta_geral, log)
    cnpjs = cnpjs_capturados(pasta_geral)
    if not gerar_pdfs:
        log("   geração de PDFs desativada — distribuindo somente os XMLs.")

    eventos_por_chave = {}
    for registro in registros:
        if registro["tipo"] != "NFSE":
            eventos_por_chave.setdefault(registro["chave"], []).append(registro["arquivo"])

    contadores = {"tomados": [0, 0, 0], "prestados": [0, 0, 0]}  # [notas, xml novos, pdf novos]
    regerados = 0  # PDFs regerados por evento (cancelamento/substituição) posterior
    processadas = 0
    for registro in registros:
        if registro["tipo"] != "NFSE":
            continue
        processadas += 1
        if processadas % 10000 == 0:
            log(f"   organizando... {processadas} nota(s) verificada(s)")
        ramos = []
        if registro["toma"] in cnpjs or registro["interm"] in cnpjs:
            ramos.append("tomados")
        if registro["prest"] in cnpjs:
            ramos.append("prestados")
        if not ramos:
            continue
        quando = registro["competencia"] or registro["emissao"][:7]
        if len(quando) < 7:
            continue
        ano, mes = quando[:4], int(quando[5:7])
        origem = completo / registro["arquivo"]
        if not origem.is_file():
            continue

        for ramo in ramos:
            estrutura = estrutura_pastas(pasta_geral, ramo)
            contadores[ramo][0] += 1

            pasta_mes_xml = estrutura["xml"] / ano / MESES_NOME[mes]
            destino_xml = pasta_mes_xml / registro["arquivo"]
            if not destino_xml.exists():
                pasta_mes_xml.mkdir(parents=True, exist_ok=True)
                shutil.copy2(_caminho_longo(origem), _caminho_longo(destino_xml))
                contadores[ramo][1] += 1
                total_xml = contadores["tomados"][1] + contadores["prestados"][1]
                if total_xml % 2000 == 0:
                    log(f"   {total_xml} XML(s) copiado(s)...")

            if not gerar_pdfs:
                continue
            pasta_mes_pdf = estrutura["pdf"] / ano / MESES_NOME[mes]
            destino_pdf = pasta_mes_pdf / _nome_pdf_nota(registro, ramo)
            eventos = eventos_por_chave.get(registro["chave"], [])
            gerar = not destino_pdf.exists()
            regerar = False
            if not gerar and eventos:
                # evento (cancelamento/substituição) baixado DEPOIS do PDF já
                # existir -> regera o PDF para estampar a marca d'água
                mtime_pdf = destino_pdf.stat().st_mtime
                regerar = any((completo / ev).is_file()
                              and (completo / ev).stat().st_mtime > mtime_pdf
                              for ev in eventos)
            if gerar or regerar:
                pasta_mes_pdf.mkdir(parents=True, exist_ok=True)
                marca = None
                for arquivo_evento in eventos:
                    dados = (completo / arquivo_evento).read_bytes()
                    if b"anc" in dados:
                        marca = "CANCELADA"
                        break
                    if b"ubst" in dados:
                        marca = "SUBSTITUÍDA"
                try:
                    gerar_pdf_nota(origem, Path(_caminho_longo(destino_pdf)), marca_dagua=marca)
                    contadores[ramo][2] += 1
                    if regerar:
                        regerados += 1
                        log(f"   PDF regerado ({marca or 'evento novo'}): {destino_pdf.name}")
                except Exception as erro:
                    log(f"   PDF falhou em {registro['arquivo']}: {erro}")
                total_pdfs = contadores["tomados"][2] + contadores["prestados"][2]
                if total_pdfs and total_pdfs % 200 == 0:
                    log(f"   {total_pdfs} PDF(s) gerado(s)...")

    for ramo, (notas, xml_novos, pdf_novos) in contadores.items():
        log(f"   {TIPOS_SERVICO[ramo]}: {notas} nota(s); {xml_novos} XML(s) e {pdf_novos} PDF(s) novos.")
    if regerados:
        log(f"   {regerados} PDF(s) regerado(s) com marca d'água por cancelamento/substituição.")


def _cartoes_planilha(linhas, tipo):
    """Cartões de estatística da capa (contagem, parceiros distintos, total)."""
    def valor_por_sufixo(linha, sufixo):
        for chave_col, valor in linha.items():
            if chave_col.endswith(sufixo):
                return valor
        return None

    total = sum(v for v in (valor_por_sufixo(l, ".vServ") for l in linhas) if isinstance(v, float))
    total_texto = f"R$ {total:,.2f}".replace(",", "@").replace(".", ",").replace("@", ".")
    if tipo == "tomados":
        parceiros = {valor_por_sufixo(l, "prest.CNPJ") for l in linhas} - {None, ""}
        return [("NOTAS RECEBIDAS", str(len(linhas)), "na competência"),
                ("PRESTADORES", str(len(parceiros)), "fornecedores distintos"),
                ("VALOR TOTAL", total_texto, "somatório dos serviços")]
    parceiros = set()
    for linha in linhas:
        parceiro = valor_por_sufixo(linha, "toma.CNPJ") or valor_por_sufixo(linha, "toma.CPF")
        if parceiro:
            parceiros.add(parceiro)
    return [("NOTAS EMITIDAS", str(len(linhas)), "na competência"),
            ("TOMADORES", str(len(parceiros)), "clientes distintos"),
            ("VALOR TOTAL", total_texto, "somatório dos serviços")]


def gerar_planilha_agrupada(pasta_geral: Path, competencia: str, log, tipo: str = "tomados"):
    """Planilha única da competência (MM/AAAA) reunindo TODAS as empresas da
    pasta geral, com a coluna Empresa identificando a origem de cada nota.
    Notas presentes em mais de uma empresa (mesma chave de acesso, ex.:
    serviço entre filiais) entram uma única vez."""
    import openpyxl

    rotulo_tipo = TIPOS_SERVICO[tipo]
    mes, ano = competencia.split("/")
    arquivos, situacoes, origem, cnpjs = [], {}, {}, set()
    vistas = set()
    for base in pastas_empresas_existentes(pasta_geral):
        pasta_mes = estrutura_pastas(base, tipo)["xml"] / ano / MESES_NOME[int(mes)]
        da_base = []
        if pasta_mes.is_dir():
            for arquivo in sorted(pasta_mes.glob("*_NFSE_*.xml")):
                m = re.search(r"_(\d{50})\.xml$", arquivo.name)
                chave = m.group(1) if m else arquivo.name
                if chave in vistas:
                    continue
                vistas.add(chave)
                da_base.append(arquivo)
                origem[arquivo.name] = base.name
        if da_base:
            arquivos += da_base
            situacoes.update(situacao_por_eventos(base))
            cnpjs |= cnpjs_capturados(base)
            log(f"   {base.name}: {len(da_base)} nota(s)")
    if not arquivos:
        log(f"   {rotulo_tipo}: nenhuma nota na competência {competencia} em nenhuma empresa.")
        return None

    log(f"   {rotulo_tipo} (agrupada): gerando planilha com {len(arquivos)} nota(s)...")
    wb = openpyxl.Workbook()
    wb.remove(wb.active)
    aba_titulo = "Notas Recebidas" if tipo == "tomados" else "Notas Emitidas"
    linhas = aba_notas(wb, aba_titulo, arquivos, situacoes, log=log, origem=origem)
    alteradas = sum(1 for l in linhas if l.get("situacao_atual") != "Normal")
    if alteradas:
        log(f"   {alteradas} nota(s) cancelada(s)/substituída(s) — ver coluna 'Situação Atual'.")
    cartoes = _cartoes_planilha(linhas, tipo)
    montar_apresentacao(wb, f"{competencia} — {rotulo_tipo} (todas as empresas)", cartoes, cnpjs)

    destino = pasta_geral / "Planilhas Agrupadas"
    destino.mkdir(parents=True, exist_ok=True)
    prefixo = "ServicosTomados" if tipo == "tomados" else "ServicosPrestados"
    arquivo_excel = destino / f"{prefixo}_Agrupada_{ano}-{mes}.xlsx"
    log(f"   gravando {arquivo_excel.name}...")
    wb.save(arquivo_excel)
    log(f"   planilha salva: {arquivo_excel}")
    return arquivo_excel


def gerar_planilha(pasta_geral: Path, competencia: str, log, tipo: str = "tomados"):
    """Gera a planilha Excel da competência (MM/AAAA) para Serviços Tomados
    ou Serviços Prestados, a partir das pastas por período."""
    import openpyxl

    rotulo_tipo = TIPOS_SERVICO[tipo]
    estrutura = estrutura_pastas(pasta_geral, tipo)
    mes, ano = competencia.split("/")
    pasta_mes = estrutura["xml"] / ano / MESES_NOME[int(mes)]
    arquivos = sorted(pasta_mes.glob("*_NFSE_*.xml")) if pasta_mes.is_dir() else []
    if not arquivos:
        log(f"   {rotulo_tipo}: nenhuma nota na competência {competencia}.")
        return None

    log(f"   {rotulo_tipo}: gerando planilha com {len(arquivos)} nota(s)...")
    wb = openpyxl.Workbook()
    wb.remove(wb.active)
    aba_titulo = "Notas Recebidas" if tipo == "tomados" else "Notas Emitidas"
    situacoes = situacao_por_eventos(pasta_geral)
    linhas = aba_notas(wb, aba_titulo, arquivos, situacoes, log=log)
    alteradas = sum(1 for l in linhas if l.get("situacao_atual") != "Normal")
    if alteradas:
        log(f"   {alteradas} nota(s) cancelada(s)/substituída(s) — ver coluna 'Situação Atual'.")
    cartoes = _cartoes_planilha(linhas, tipo)
    montar_apresentacao(wb, f"{competencia} — {rotulo_tipo}", cartoes, cnpjs_capturados(pasta_geral))

    estrutura["planilhas"].mkdir(parents=True, exist_ok=True)
    prefixo = "ServicosTomados" if tipo == "tomados" else "ServicosPrestados"
    arquivo_excel = estrutura["planilhas"] / f"{prefixo}_{ano}-{mes}.xlsx"
    log(f"   gravando {arquivo_excel.name}...")
    wb.save(arquivo_excel)
    log(f"   planilha salva: {arquivo_excel}")
    return arquivo_excel


# ----------------------------------------------------------------------------
# Agendamento automático (Agendador de Tarefas do Windows) e captura silenciosa
# ----------------------------------------------------------------------------

NOME_TAREFA = "SolucoesFiscais_Captura"
FREQUENCIAS = {"Diária": ["/SC", "DAILY"],
               "Semanal": ["/SC", "WEEKLY"],
               "Quinzenal": ["/SC", "WEEKLY", "/MO", "2"],
               "Mensal": ["/SC", "MONTHLY"]}


def _comando_captura() -> str:
    if getattr(sys, "frozen", False) or "__compiled__" in globals():
        return f'"{_caminho_programa()}" --capturar'
    return f'"{sys.executable}" "{Path(__file__).resolve()}" --capturar'


def criar_agendamento(frequencia: str, hora: str):
    argumentos = ["schtasks", "/Create", "/F", "/TN", NOME_TAREFA,
                  "/TR", _comando_captura(), "/ST", hora] + FREQUENCIAS[frequencia]
    resultado = subprocess.run(argumentos, capture_output=True, creationflags=CRIAR_SEM_JANELA)
    saida = (resultado.stdout + resultado.stderr).decode("cp850", errors="replace").strip()
    return resultado.returncode == 0, saida


def remover_agendamento():
    resultado = subprocess.run(["schtasks", "/Delete", "/F", "/TN", NOME_TAREFA],
                               capture_output=True, creationflags=CRIAR_SEM_JANELA)
    saida = (resultado.stdout + resultado.stderr).decode("cp850", errors="replace").strip()
    return resultado.returncode == 0, saida


def executar_captura_automatica() -> int:
    """Modo silencioso (--capturar): baixa os XMLs e organiza as pastas, sem interface."""
    config = json.loads(ARQ_CONFIG.read_text(encoding="utf-8")) if ARQ_CONFIG.is_file() else {}
    pasta_geral = pasta_geral_base()
    registro = open(pasta_geral / "registro_capturas.log", "a", encoding="utf-8")

    def log(mensagem):
        registro.write(f"{datetime.now().strftime('%d/%m/%Y %H:%M:%S')}  {mensagem}\n")
        registro.flush()

    log("=== captura automática iniciada ===")
    try:
        resultado_licenca = licenca_armazenada()
        if resultado_licenca is None or resultado_licenca[0] < date.today():
            log("licença ausente ou vencida — captura abortada.")
            return 1
        validade, plano = resultado_licenca
        limite_cnpj = LIMITES_PLANO.get(plano, 1)
        selecionados = list(dict.fromkeys(config.get("certificados", [])))
        if len(selecionados) > limite_cnpj:
            log(f"aviso: licença ({plano}) permite só {limite_cnpj} CNPJ(s); "
                f"usando os primeiros {limite_cnpj} configurados.")
            selecionados = selecionados[:limite_cnpj]
        selecionados = set(selecionados)
        certificados = [c for c in listar_certificados()
                        if not selecionados or c["thumbprint"] in selecionados]
        if not certificados:
            log("nenhum certificado disponível — captura abortada.")
            return 1
        bases = []
        for cert in certificados:
            log(f"capturando {cert['cnpj']} ({cert['nome'][:40]})...")
            try:
                bases.append(capturar_certificado(cert, pasta_geral, log))
            except Exception as erro:
                log(f"ERRO em {cert['cnpj']}: {erro}")
        for base in dict.fromkeys(bases):
            log(f"organizando {base.name}...")
            organizar_periodos(base, log, bool(config.get("gerar_pdf", True)))
        log("=== captura automática concluída ===")
        return 0
    finally:
        registro.close()


def gerar_icone(destino: Path):
    """Gera o .ico do aplicativo (cabeça do robô) para janela e executável."""
    try:
        from PIL import Image
    except ImportError:
        return None
    png = PASTA_APP / "robo.png"
    if not png.is_file() and desenhar_robo(png) is None:
        return None
    imagem = Image.open(png).convert("RGBA")
    quadrado = imagem.crop((60, 10, 420, 370))
    quadrado.save(destino, format="ICO",
                  sizes=[(256, 256), (64, 64), (48, 48), (32, 32), (16, 16)])
    return destino


# ----------------------------------------------------------------------------
# Interface gráfica
# ----------------------------------------------------------------------------

def executar_app():
    import tkinter as tk
    from tkinter import messagebox, ttk

    AZUL = "#1F3864"
    AZUL_ESCURO = "#142848"
    AZUL_MEDIO = "#2E5EA8"
    OURO = "#F2A900"
    VERDE = "#2E7D32"
    FUNDO = "#EEF2F8"
    BORDA = "#C9D6EA"

    # identidade própria na barra de tarefas (senão o Windows usa ícone genérico)
    try:
        import ctypes
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("SolucoesFiscais.CapturaNFSe")
    except Exception:
        pass

    raiz = tk.Tk()
    raiz.withdraw()
    PASTA_APP.mkdir(parents=True, exist_ok=True)
    try:
        caminho_icone = gerar_icone(PASTA_APP / "icone.ico")
    except Exception:
        caminho_icone = None

    def aplicar_icone(janela):
        if caminho_icone:
            try:
                janela.iconbitmap(str(caminho_icone))
            except Exception:
                pass

    aplicar_icone(raiz)
    try:
        from PIL import Image, ImageTk
        png_icone = PASTA_APP / "robo.png"
        if png_icone.is_file():
            recorte = Image.open(png_icone).crop((60, 10, 420, 370))
            fotos_icone = [ImageTk.PhotoImage(recorte.resize(t))
                           for t in ((16, 16), (32, 32), (48, 48), (64, 64))]
            raiz.iconphoto(True, *fotos_icone)
            raiz._icones = fotos_icone  # referência viva para o Tk não descartar
    except Exception:
        pass

    # --- licença -------------------------------------------------------------
    resultado_licenca = licenca_armazenada()
    validade = resultado_licenca[0] if resultado_licenca else None
    plano_ativo = resultado_licenca[1] if resultado_licenca else "E"
    while validade is None or validade < date.today():
        janela = tk.Toplevel(raiz)
        janela.title(f"{APP_NOME} — Ativação")
        janela.configure(bg="white")
        janela.geometry("460x260")
        janela.resizable(False, False)
        aplicar_icone(janela)
        topo_ativacao = tk.Frame(janela, bg=AZUL)
        topo_ativacao.pack(fill="x")
        tk.Label(topo_ativacao, text="SOLUÇÕES FISCAIS", bg=AZUL, fg="white",
                 font=("Segoe UI", 14, "bold")).pack(pady=(10, 0))
        tk.Label(topo_ativacao, text="Captura de NFS-e — Padrão Nacional", bg=AZUL,
                 fg="#9FC5FF", font=("Segoe UI", 9)).pack(pady=(0, 10))
        tk.Frame(janela, bg=OURO, height=3).pack(fill="x")
        tk.Label(janela, text="Informe o código de ativação recebido por e-mail:", bg="white",
                 font=("Segoe UI", 10)).pack(pady=(20, 6))
        tk.Label(janela, text="A ativação vale somente para este computador.", bg="white",
                 fg="#888888", font=("Segoe UI", 8, "italic")).pack()
        entrada = tk.Entry(janela, width=30, font=("Consolas", 12), justify="center",
                           relief="solid", bd=1)
        entrada.pack()
        entrada.focus_set()
        aviso = tk.Label(janela, text="", fg="#C62828", bg="white", font=("Segoe UI", 9))
        aviso.pack(pady=4)
        resultado = {"validade": None, "plano": "E"}

        def ativar():
            codigo = entrada.get()
            resultado_validacao = validar_chave(codigo)
            if resultado_validacao is None:
                aviso.config(text="Código inválido. Verifique com a Soluções Fiscais.")
            else:
                valida, plano_codigo = resultado_validacao
                if valida < date.today():
                    aviso.config(text=f"Código expirado em {valida.strftime('%d/%m/%Y')}.")
                elif consultar_revogacao_online(codigo) == "revogada":
                    aviso.config(text="Este código foi revogado. Contate a Soluções Fiscais.")
                else:
                    guardar_licenca(codigo)
                    resultado["validade"] = valida
                    resultado["plano"] = plano_codigo
                    janela.destroy()

        tk.Button(janela, text="ATIVAR", command=ativar, bg=OURO, fg=AZUL_ESCURO,
                  font=("Segoe UI", 10, "bold"), relief="flat", padx=26, pady=6,
                  cursor="hand2").pack(pady=6)
        entrada.bind("<Return>", lambda evento: ativar())
        janela.protocol("WM_DELETE_WINDOW", janela.destroy)
        janela.grab_set()
        raiz.wait_window(janela)
        validade = resultado["validade"]
        plano_ativo = resultado.get("plano", plano_ativo)
        if validade is None:
            raiz.destroy()
            return

    # --- configuração --------------------------------------------------------
    config = {}
    if ARQ_CONFIG.is_file():
        config = json.loads(ARQ_CONFIG.read_text(encoding="utf-8"))

    raiz.deiconify()
    raiz.title(APP_TITULO)
    raiz.configure(bg=FUNDO)
    raiz.geometry("930x790")
    raiz.minsize(880, 720)

    estilo = ttk.Style(raiz)
    try:
        estilo.theme_use("clam")
    except Exception:
        pass
    estilo.configure("Treeview", font=("Segoe UI", 9), rowheight=22,
                     fieldbackground="white", background="white", borderwidth=0)
    estilo.configure("Treeview.Heading", font=("Segoe UI", 9, "bold"),
                     background=AZUL, foreground="white", relief="flat")
    estilo.map("Treeview.Heading", background=[("active", AZUL_MEDIO)])
    estilo.map("Treeview", background=[("selected", AZUL_MEDIO)],
               foreground=[("selected", "white")])

    # --- cabeçalho -----------------------------------------------------------
    cabecalho = tk.Frame(raiz, bg=AZUL)
    cabecalho.pack(fill="x")
    try:
        from PIL import Image, ImageTk
        png_robo = PASTA_APP / "robo.png"
        if not png_robo.is_file():
            desenhar_robo(png_robo)
        foto_robo = ImageTk.PhotoImage(Image.open(png_robo).crop((60, 10, 420, 370)).resize((54, 54)))
        rotulo_robo = tk.Label(cabecalho, image=foto_robo, bg=AZUL)
        rotulo_robo.image = foto_robo
        rotulo_robo.pack(side="left", padx=(18, 10), pady=10)
    except Exception:
        pass
    bloco_titulo = tk.Frame(cabecalho, bg=AZUL)
    bloco_titulo.pack(side="left", pady=10)
    tk.Label(bloco_titulo, text="SOLUÇÕES FISCAIS", bg=AZUL, fg="white",
             font=("Segoe UI", 17, "bold")).pack(anchor="w")
    tk.Label(bloco_titulo, text="Captura de NFS-e  •  Padrão Nacional (Portal Nacional / ADN)",
             bg=AZUL, fg="#9FC5FF", font=("Segoe UI", 9)).pack(anchor="w")
    dias = (validade - date.today()).days
    tk.Label(cabecalho, text=f"Licença até {validade.strftime('%d/%m/%Y')}  •  {dias} dia(s)",
             bg=AZUL, fg="#B7F0C0" if dias > 7 else "#FFB4A9",
             font=("Segoe UI", 9, "bold")).pack(side="right", padx=18)
    tk.Frame(raiz, bg=OURO, height=4).pack(fill="x")

    corpo = tk.Frame(raiz, bg=FUNDO)
    corpo.pack(fill="both", expand=True, padx=14, pady=10)

    def cartao(titulo):
        quadro = tk.LabelFrame(corpo, text=f"  {titulo}  ", bg="white", fg=AZUL,
                               font=("Segoe UI", 10, "bold"), bd=0,
                               highlightbackground=BORDA, highlightthickness=1)
        quadro.pack(fill="x", pady=5)
        return quadro

    def botao(pai, texto, cor, comando=None, fg="white"):
        return tk.Button(pai, text=texto, bg=cor, fg=fg, font=("Segoe UI", 10, "bold"),
                         relief="flat", padx=14, pady=6, cursor="hand2",
                         activebackground=AZUL_ESCURO, activeforeground="white",
                         command=comando)

    # --- pasta base (fixa em Documentos deste computador) --------------------
    pasta_base = pasta_geral_base()
    quadro_pasta = cartao("Pasta base — criada automaticamente em Documentos deste computador; uma pasta por empresa")
    tk.Label(quadro_pasta, text=str(pasta_base), bg="white", fg="#333333",
             font=("Segoe UI", 9)).pack(side="left", padx=10, pady=10)

    def abrir_pasta_base():
        try:
            os.startfile(str(pasta_base))
        except OSError:
            pass

    botao(quadro_pasta, "Abrir pasta", "#5B6B85", abrir_pasta_base).pack(side="right", padx=10, pady=8)

    # --- certificados ----------------------------------------------------------
    quadro_cert = cartao("Certificados digitais instalados — selecione um ou mais (Ctrl + clique)")
    arvore = ttk.Treeview(quadro_cert, columns=("cnpj", "empresa", "validade"),
                          show="headings", height=7, selectmode="extended")
    arvore.heading("cnpj", text="CNPJ")
    arvore.heading("empresa", text="Empresa")
    arvore.heading("validade", text="Válido até")
    arvore.column("cnpj", width=140, anchor="w")
    arvore.column("empresa", width=440, anchor="w")
    arvore.column("validade", width=90, anchor="center")
    arvore.pack(side="left", fill="both", expand=True, padx=(10, 0), pady=10)
    barra_cert = ttk.Scrollbar(quadro_cert, orient="vertical", command=arvore.yview)
    barra_cert.pack(side="left", fill="y", pady=10)
    arvore.configure(yscrollcommand=barra_cert.set)

    certificados = []

    def recarregar_certificados():
        arvore.delete(*arvore.get_children())
        certificados.clear()
        try:
            certificados.extend(listar_certificados())
        except Exception as erro:
            messagebox.showerror(APP_NOME, f"Falha ao listar certificados:\n{erro}")
            return
        selecionados_config = set(config.get("certificados", []))
        for indice, cert in enumerate(certificados):
            arvore.insert("", "end", iid=str(indice),
                          values=(cert["cnpj"], cert["nome"][:60], cert["validade"]))
            if cert["thumbprint"] in selecionados_config:
                arvore.selection_add(str(indice))

    botao(quadro_cert, "Atualizar", "#5B6B85", recarregar_certificados).pack(side="right", padx=10)

    # --- ações (duas linhas para nada ficar cortado) ---------------------------
    quadro_acao = cartao("Ações")
    linha_busca = tk.Frame(quadro_acao, bg="white")
    linha_busca.pack(fill="x", padx=10, pady=(10, 4))
    botao_buscar = botao(linha_busca, "▶   1. BUSCAR XMLs AGORA", AZUL)
    botao_buscar.pack(side="left")
    tk.Label(linha_busca, text="baixa os XMLs e organiza Tomados e Prestados por período",
             bg="white", fg="#888888", font=("Segoe UI", 8, "italic")).pack(side="left", padx=12)
    var_pdf = tk.BooleanVar(value=bool(config.get("gerar_pdf", True)))
    tk.Checkbutton(linha_busca, text="Gerar PDFs (mais lento)", variable=var_pdf,
                   bg="white", activebackground="white", fg="#333333",
                   font=("Segoe UI", 9)).pack(side="left", padx=(4, 0))

    linha_planilha = tk.Frame(quadro_acao, bg="white")
    linha_planilha.pack(fill="x", padx=10, pady=(4, 10))
    tk.Label(linha_planilha, text="Competência:", bg="white", fg="#333333",
             font=("Segoe UI", 9)).pack(side="left")
    var_mes = tk.StringVar(value=f"{date.today().month:02d}")
    var_ano = tk.StringVar(value=str(date.today().year))
    ttk.Combobox(linha_planilha, textvariable=var_mes, width=4, state="readonly",
                 values=[f"{m:02d}" for m in range(1, 13)]).pack(side="left", padx=3)
    ttk.Combobox(linha_planilha, textvariable=var_ano, width=6, state="readonly",
                 values=[str(a) for a in range(2023, date.today().year + 2)]).pack(side="left", padx=3)
    tk.Label(linha_planilha, text="Serviços:", bg="white", fg="#333333",
             font=("Segoe UI", 9)).pack(side="left", padx=(12, 3))
    var_tipo = tk.StringVar(value="Tomados")
    ttk.Combobox(linha_planilha, textvariable=var_tipo, width=10, state="readonly",
                 values=["Tomados", "Prestados", "Os 2"]).pack(side="left", padx=3)
    tk.Label(linha_planilha, text="Saída:", bg="white", fg="#333333",
             font=("Segoe UI", 9)).pack(side="left", padx=(12, 3))
    var_saida = tk.StringVar(value=config.get("planilha_saida", "Por CNPJ"))
    ttk.Combobox(linha_planilha, textvariable=var_saida, width=9, state="readonly",
                 values=["Por CNPJ", "Agrupada"]).pack(side="left", padx=3)
    botao_planilha = botao(linha_planilha, "📊   2. GERAR PLANILHA EXCEL", VERDE)
    botao_planilha.pack(side="left", padx=14)

    # --- agendamento -------------------------------------------------------------
    quadro_agenda = cartao("Captura automática — agendamento no Windows")
    tk.Label(quadro_agenda, text="Frequência:", bg="white",
             font=("Segoe UI", 9)).pack(side="left", padx=(10, 4), pady=10)
    var_freq = tk.StringVar(value=config.get("agendamento", {}).get("frequencia", "Diária"))
    ttk.Combobox(quadro_agenda, textvariable=var_freq, width=11, state="readonly",
                 values=list(FREQUENCIAS)).pack(side="left")
    tk.Label(quadro_agenda, text="Horário:", bg="white",
             font=("Segoe UI", 9)).pack(side="left", padx=(12, 4))
    var_hora = tk.StringVar(value=config.get("agendamento", {}).get("hora", "08:00"))
    tk.Entry(quadro_agenda, textvariable=var_hora, width=7, justify="center",
             font=("Segoe UI", 9), relief="solid", bd=1).pack(side="left")
    situacao_agenda = tk.Label(quadro_agenda, bg="white", fg="#888888",
                               font=("Segoe UI", 8, "italic"))
    situacao_agenda.pack(side="right", padx=10)

    def atualizar_situacao_agenda():
        agendamento = config.get("agendamento")
        if agendamento:
            situacao_agenda.config(fg=VERDE,
                                   text=f"Ativo: {agendamento['frequencia'].lower()} às {agendamento['hora']}")
        else:
            situacao_agenda.config(fg="#888888", text="Nenhum agendamento ativo")

    # --- registro de atividades ---------------------------------------------------
    quadro_log = tk.LabelFrame(corpo, text="  Registro de atividades  ", bg="white", fg=AZUL,
                               font=("Segoe UI", 10, "bold"), bd=0,
                               highlightbackground=BORDA, highlightthickness=1)
    quadro_log.pack(fill="both", expand=True, pady=5)
    registro_log = tk.Text(quadro_log, height=10, state="disabled", font=("Consolas", 9),
                           bg="#101F3C", fg="#BFE0FF", insertbackground="white",
                           relief="flat", padx=8, pady=6)
    registro_log.pack(fill="both", expand=True, padx=10, pady=10)

    fila = queue.Queue()

    def log(mensagem):
        fila.put(mensagem)
        # espelha o log da tela em registro_capturas.log (mesmo arquivo da captura
        # automática) para diagnóstico remoto — a janela não persiste após fechar
        try:
            with open(pasta_geral_base() / "registro_capturas.log", "a", encoding="utf-8") as registro:
                registro.write(f"{datetime.now().strftime('%d/%m/%Y %H:%M:%S')}  {mensagem}\n")
        except OSError:
            pass

    def despejar_fila():
        while not fila.empty():
            mensagem = fila.get()
            registro_log.config(state="normal")
            registro_log.insert("end", mensagem + "\n")
            registro_log.see("end")
            registro_log.config(state="disabled")
        raiz.after(200, despejar_fila)

    despejar_fila()

    def salvar_config():
        limite_cnpj = LIMITES_PLANO.get(plano_ativo, 1)
        selecionados_atual = [certificados[int(i)]["thumbprint"] for i in arvore.selection()]
        if len(selecionados_atual) > limite_cnpj:
            messagebox.showwarning(
                APP_NOME,
                f"Sua licença ({plano_ativo}) permite selecionar até {limite_cnpj} "
                f"CNPJ(s). Você selecionou {len(selecionados_atual)} — desmarque "
                f"alguns antes de continuar."
            )
            return False
        config.pop("pasta_geral", None)  # a pasta base agora é fixa (Documentos)
        config["gerar_pdf"] = bool(var_pdf.get())
        config["planilha_saida"] = var_saida.get()
        config["certificados"] = selecionados_atual
        PASTA_APP.mkdir(parents=True, exist_ok=True)
        ARQ_CONFIG.write_text(json.dumps(config), encoding="utf-8")
        return True

    def em_execucao(executando):
        estado = "disabled" if executando else "normal"
        for botao_acao in (botao_buscar, botao_planilha, botao_agendar, botao_remover):
            botao_acao.config(state=estado)

    def acao_buscar():
        selecao = [certificados[int(i)] for i in arvore.selection()]
        if not selecao:
            messagebox.showwarning(APP_NOME, "Selecione ao menos um certificado na lista.")
            return
        if not salvar_config():
            return
        pasta = pasta_geral_base()

        gerar_pdfs = bool(var_pdf.get())

        def trabalho():
            log(f"Iniciando busca de XMLs para {len(selecao)} certificado(s)...")
            bases = []
            for cert in selecao:
                log(f"-> {cert['cnpj']} {cert['nome'][:40]}")
                try:
                    bases.append(capturar_certificado(cert, pasta, log))
                except Exception as erro:
                    log(f"   ERRO: {erro}")
            log("Organizando pastas por período de cada empresa...")
            for base in dict.fromkeys(bases):
                log(f"-> {base.name}")
                try:
                    organizar_periodos(base, log, gerar_pdfs)
                except Exception as erro:
                    log(f"   ERRO na organização: {erro}")
            log("Busca concluída. XMLs e PDFs prontos nas pastas por período.\n")
            em_execucao(False)

        em_execucao(True)
        threading.Thread(target=trabalho, daemon=True).start()

    def acao_planilha():
        if not salvar_config():
            return
        pasta = pasta_geral_base()
        competencia = f"{var_mes.get()}/{var_ano.get()}"
        escolha = var_tipo.get()
        saida = var_saida.get()
        tipos = {"Tomados": ["tomados"], "Prestados": ["prestados"],
                 "Os 2": ["tomados", "prestados"]}[escolha]

        def trabalho():
            log(f"Gerando planilhas da competência {competencia} "
                f"({escolha.lower()}, {saida.lower()})...")
            empresas = pastas_empresas_existentes(pasta)
            if not empresas:
                log("   nenhuma pasta de empresa encontrada. Rode a busca (passo 1) primeiro.\n")
                em_execucao(False)
                return
            geradas = 0
            if saida == "Agrupada":
                for tipo in tipos:
                    try:
                        if gerar_planilha_agrupada(pasta, competencia, log, tipo=tipo):
                            geradas += 1
                    except Exception as erro:
                        log(f"   ERRO ({TIPOS_SERVICO[tipo]} agrupada): {erro}")
            else:
                for base in empresas:
                    log(f"-> {base.name}")
                    for tipo in tipos:
                        try:
                            if gerar_planilha(base, competencia, log, tipo=tipo):
                                geradas += 1
                        except Exception as erro:
                            log(f"   ERRO ({TIPOS_SERVICO[tipo]}): {erro}")
            log(f"{geradas} planilha(s) gerada(s).\n")
            em_execucao(False)

        em_execucao(True)
        threading.Thread(target=trabalho, daemon=True).start()

    def acao_agendar():
        hora = var_hora.get().strip()
        if not re.fullmatch(r"([01]\d|2[0-3]):[0-5]\d", hora):
            messagebox.showwarning(APP_NOME, "Horário inválido. Use o formato HH:MM, ex.: 08:00.")
            return
        if not arvore.selection():
            messagebox.showwarning(APP_NOME, "Selecione os certificados que a captura automática deve usar.")
            return
        if not salvar_config():
            return
        ok, saida = criar_agendamento(var_freq.get(), hora)
        if ok:
            config["agendamento"] = {"frequencia": var_freq.get(), "hora": hora}
            ARQ_CONFIG.write_text(json.dumps(config), encoding="utf-8")
            atualizar_situacao_agenda()
            log(f"Captura automática agendada: {var_freq.get().lower()} às {hora}.")
            messagebox.showinfo(APP_NOME,
                                f"Captura automática agendada ({var_freq.get().lower()} às {hora}).\n"
                                "Os XMLs e PDFs ficarão prontos nas pastas por período; gere a planilha quando quiser.")
        else:
            log(f"Falha ao agendar: {saida}")
            messagebox.showerror(APP_NOME, f"Não foi possível criar o agendamento:\n{saida}")

    def acao_remover_agenda():
        ok, saida = remover_agendamento()
        config.pop("agendamento", None)
        ARQ_CONFIG.write_text(json.dumps(config), encoding="utf-8")
        atualizar_situacao_agenda()
        log("Agendamento removido." if ok else f"Agendamento: {saida}")

    botao_agendar = botao(quadro_agenda, "ATIVAR", OURO, acao_agendar, fg=AZUL_ESCURO)
    botao_agendar.pack(side="left", padx=(14, 4))
    botao_remover = botao(quadro_agenda, "Remover", "#8A94A6", acao_remover_agenda)
    botao_remover.pack(side="left")

    botao_buscar.config(command=acao_buscar)
    botao_planilha.config(command=acao_planilha)

    recarregar_certificados()
    atualizar_situacao_agenda()
    log(f"Bem-vindo à {APP_NOME}! Licença ativa até {validade.strftime('%d/%m/%Y')}.")
    log("Passo 1: selecione os certificados e busque os XMLs (ou deixe a captura automática agendada).")
    log(f"Pasta base deste computador: {pasta_base}")
    log(r"Estrutura: Pasta base\CNPJ - Razão Social\Originais -> Período Completo +")
    log(r"           Serviços Tomados e Serviços Prestados (XML, PDF e Planilhas por período).")
    log("Passo 2: escolha a competência e o tipo (Tomados, Prestados ou Os 2) e gere as planilhas.\n")

    if os.environ.get("SF_CAPTURA_TELA"):
        def capturar_tela():
            try:
                from PIL import ImageGrab
                raiz.update_idletasks()
                x, y = raiz.winfo_rootx(), raiz.winfo_rooty()
                ImageGrab.grab((x, y, x + raiz.winfo_width(), y + raiz.winfo_height())).save(
                    os.environ["SF_CAPTURA_TELA"])
            finally:
                raiz.destroy()
        raiz.after(1500, capturar_tela)

    raiz.mainloop()


if __name__ == "__main__":
    if os.environ.get("SF_DEBUG_CAMINHOS"):
        # diagnóstico de build: grava onde o programa enxerga a si mesmo e a
        # pasta de NSU (verificação do onefile), sem abrir a interface
        Path(os.environ["SF_DEBUG_CAMINHOS"]).write_text(json.dumps({
            "argv0": sys.argv[0], "executable": sys.executable, "arquivo": __file__,
            "frozen": bool(getattr(sys, "frozen", False)),
            "compilado": repr(globals().get("__compiled__")),
            "caminho_programa": str(_caminho_programa()),
            "pasta_nsu": str(pasta_nsu())}, indent=2, ensure_ascii=False), encoding="utf-8")
        sys.exit(0)
    if "--capturar" in sys.argv:
        sys.exit(executar_captura_automatica())
    executar_app()

