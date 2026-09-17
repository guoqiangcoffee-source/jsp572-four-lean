param(
  [string]$LeanBin = '',
  [switch]$FromArchive
)

$ErrorActionPreference = 'Stop'
$proofProject = Split-Path -Parent $PSScriptRoot
if (-not $LeanBin) {
  $workspaceToolchain = Join-Path $proofProject '../../work/lean-4.35.0-rc2-windows/bin'
  if (Test-Path -LiteralPath $workspaceToolchain) {
    $LeanBin = (Resolve-Path -LiteralPath $workspaceToolchain).Path
  } else {
    $LeanBin = Split-Path -Parent (Get-Command lean.exe -ErrorAction Stop).Source
  }
}
$LeanBin = (Resolve-Path -LiteralPath $LeanBin).Path
$env:PATH = "$LeanBin;$env:PATH"
$env:LEAN_ABORT_ON_PANIC = '1'
$exportPath = Join-Path $PSScriptRoot 'jsp572-four-complete.ndjson'

function Invoke-ExternalChecker {
  param([string]$Name, [string]$Executable, [string[]]$CheckerArguments)
  $logPath = Join-Path $PSScriptRoot "external-$Name.log"
  $errorPath = Join-Path $PSScriptRoot "external-$Name-stderr.log"
  $process = Start-Process -FilePath (Join-Path $LeanBin $Executable) `
    -ArgumentList $CheckerArguments -WorkingDirectory $PSScriptRoot `
    -WindowStyle Hidden -Wait -PassThru `
    -RedirectStandardOutput $logPath -RedirectStandardError $errorPath
  Set-Content -LiteralPath (Join-Path $PSScriptRoot "external-$Name-status.log") `
    -Value "exit_code=$($process.ExitCode)"
  if ($process.ExitCode -ne 0) { throw "$Name rejected the export (exit $($process.ExitCode))." }
}

if ($FromArchive) {
  $inputStream = [IO.File]::OpenRead((Join-Path $PSScriptRoot 'jsp572-four-complete.ndjson.gz'))
  try {
    $gzipStream = [IO.Compression.GZipStream]::new($inputStream, [IO.Compression.CompressionMode]::Decompress)
    try {
      $outputStream = [IO.File]::Create($exportPath)
      try { $gzipStream.CopyTo($outputStream) } finally { $outputStream.Dispose() }
    } finally { $gzipStream.Dispose() }
  } finally { $inputStream.Dispose() }
  $expected = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'external-check-metadata.json') -Raw | ConvertFrom-Json
  $actual = (Get-FileHash -LiteralPath $exportPath -Algorithm SHA256).Hash.ToLowerInvariant()
  if ($actual -ne $expected.exportSha256) { throw 'Archived export SHA256 mismatch.' }
} else {
  # Build the project separately before this step. '--' selects a declaration;
  # leanexport automatically includes that declaration's dependency closure.
  $process = Start-Process -FilePath (Join-Path $LeanBin 'lake.exe') `
    -ArgumentList @('env', 'leanexport', 'JSP572Four.Main', '--', 'JSP572Four.jsp572_four_complete') `
    -WorkingDirectory $proofProject -WindowStyle Hidden -Wait -PassThru `
    -RedirectStandardOutput $exportPath `
    -RedirectStandardError (Join-Path $PSScriptRoot 'external-export-stderr.log')
  Set-Content -LiteralPath (Join-Path $PSScriptRoot 'external-export-status.log') `
    -Value "exit_code=$($process.ExitCode)"
  if ($process.ExitCode -ne 0) { throw "Export failed (exit $($process.ExitCode))." }
}

Invoke-ExternalChecker -Name 'lean4lean' -Executable 'lean4lean.exe' `
  -CheckerArguments @('--import', 'jsp572-four-complete.ndjson')
Invoke-ExternalChecker -Name 'nanoda' -Executable 'nanoda_bin.exe' `
  -CheckerArguments @('external-nanoda-config.json')

Write-Output 'Both external checkers accepted the export.'
Write-Output "Export SHA256: $((Get-FileHash -LiteralPath $exportPath -Algorithm SHA256).Hash.ToLowerInvariant())"
