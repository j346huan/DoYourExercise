$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath $PSScriptRoot
$exerciseNode = (Get-Command node -ErrorAction SilentlyContinue).Source
if ($exerciseNode) {
  $exerciseNodeMajor = [int]((& $exerciseNode --version).TrimStart('v').Split('.')[0])
  if ($exerciseNodeMajor -lt 22) { $exerciseNode = $null }
}
if (-not $exerciseNode) {
  $exerciseBundled = Get-ChildItem -Path (Join-Path $PSScriptRoot '.tools/node22') -Filter node.exe -File -Recurse -ErrorAction SilentlyContinue | Select-Object -First 1
  if ($exerciseBundled) { $exerciseNode = $exerciseBundled.FullName }
}
if (-not $exerciseNode) { throw 'Install Node.js 22 or newer, then run this script again.' }
if (-not (Test-Path -LiteralPath (Join-Path $PSScriptRoot 'node_modules'))) { throw 'Run npm ci once before starting the notebook.' }
& $exerciseNode scripts/dev.mjs
