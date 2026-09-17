$ErrorActionPreference = 'Stop'
Push-Location $PSScriptRoot
try {
  New-Item -ItemType Directory -Force verification | Out-Null
  & lake build JSP572Four 2>&1 | Tee-Object verification/build.log
  if ($LASTEXITCODE -ne 0) { throw 'Lean build failed.' }
  & lake env lean Audit.lean 2>&1 | Tee-Object verification/axioms.log
  if ($LASTEXITCODE -ne 0) { throw 'Axiom audit failed.' }
  Write-Output 'Complete theorem build and axiom allowlist audit passed.'
} finally {
  Pop-Location
}
