param(
  [string]$LeanBin = 'D:/Programs/Lean/Elan/toolchains/leanprover--lean4---v4.33.1/bin'
)

$ErrorActionPreference = 'Stop'
[Diagnostics.Process]::GetCurrentProcess().PriorityClass = 'Idle'
$taskRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $taskRoot
$env:ELAN_HOME = 'D:/Programs/Lean/Elan'
$env:GIT_CONFIG_COUNT = '2'
$env:GIT_CONFIG_KEY_0 = 'safe.directory'
$env:GIT_CONFIG_VALUE_0 = 'D:/Programs/Lean/lake-packages/E252/*'
$env:GIT_CONFIG_KEY_1 = 'safe.directory'
$env:GIT_CONFIG_VALUE_1 = $taskRoot + '/.lake/packages/*'

$taskLabel = 'generalizations-' + [DateTime]::UtcNow.ToString('yyyyMMdd-HHmmss') +
  '-' + [Guid]::NewGuid().ToString('N').Substring(0, 8)
$taskFresh = Join-Path $taskRoot ('.lake/build/' + $taskLabel)
$taskLib = Join-Path $taskFresh 'lib/lean'
if (Test-Path -LiteralPath $taskFresh) { throw 'Fresh output directory already exists' }
New-Item -ItemType Directory -Path $taskLib | Out-Null
$taskStarted = [DateTime]::UtcNow
$taskHashes = @{}
$taskFiles = @('Erdos252/Solution.lean', 'Erdos252.lean', 'audit/Statement.lean',
  'Generalizations.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain') +
  @(Get-ChildItem -LiteralPath (Join-Path $taskRoot 'Generalizations') -File |
    ForEach-Object { 'Generalizations/' + $_.Name })
foreach ($taskFile in $taskFiles) {
  $taskHashes[$taskFile] = (Get-FileHash -LiteralPath (Join-Path $taskRoot $taskFile)).Hash
}

function Invoke-Check {
  param([string]$Name, [string]$Exe, [string[]]$Arguments)
  $taskLog = Join-Path $taskFresh ($Name + '.log')
  Write-Output ('Checking ' + $Name)
  $savedErrorAction = $ErrorActionPreference
  $ErrorActionPreference = 'Continue'
  & $Exe @Arguments *> $taskLog
  $taskCode = $LASTEXITCODE
  $ErrorActionPreference = $savedErrorAction
  if ($taskCode -ne 0) {
    Get-Content -LiteralPath $taskLog
    throw ('Failed {0} (exit {1}); see {2}' -f $Name, $taskCode, $taskLog)
  }
  $taskText = [string](Get-Content -LiteralPath $taskLog -Raw)
  if ($taskText -match '(?im)\bwarning:|\berror:|sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler') {
    Get-Content -LiteralPath $taskLog
    throw ('Unexpected diagnostic in ' + $Name)
  }
  Write-Output ('PASS ' + $Name)
}

Invoke-Check 'build' (Join-Path $LeanBin 'lake.exe') `
  @('--wfail', 'build', 'Erdos252', 'Generalizations')
$env:LEAN_PATH = (@($taskLib) + @(Get-ChildItem -LiteralPath `
    (Join-Path $taskRoot '.lake/packages') -Directory | ForEach-Object {
  $taskDependency = Join-Path $_.FullName '.lake/build/lib/lean'
  if (Test-Path -LiteralPath $taskDependency) { $taskDependency }
})) -join ';'
$taskOptions = @('--trust=0', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
  '-Dwarn.sorry=true', ('--root=' + $taskRoot))
$taskModules = @('Erdos252.Solution', 'Erdos252', 'Generalizations.Cantor',
  'Generalizations.Examples', 'Generalizations.WeightedTail', 'Generalizations.Joint',
  'Generalizations.Instances', 'Generalizations.Denominator', 'Generalizations',
  'Generalizations.Audit')
foreach ($taskModule in $taskModules) {
  $taskRelative = $taskModule.Replace('.', '/')
  $taskOutput = Join-Path $taskLib ($taskRelative + '.olean')
  New-Item -ItemType Directory -Path (Split-Path -Parent $taskOutput) -Force | Out-Null
  Invoke-Check ('trust0-' + $taskModule) (Join-Path $LeanBin 'lean.exe') `
    ($taskOptions + @('-o', $taskOutput, (Join-Path $taskRoot ($taskRelative + '.lean'))))
}
Invoke-Check 'statement-original' (Join-Path $LeanBin 'lean.exe') `
  ($taskOptions + @((Join-Path $taskRoot 'audit/Statement.lean')))

$taskAudit = [string](Get-Content -LiteralPath `
  (Join-Path $taskFresh 'trust0-Generalizations.Audit.log') -Raw)
$taskReports = [regex]::Matches($taskAudit,
  '''(?<decl>[^'']+)'' depends on axioms: \[(?<axioms>[^\]]*)\]')
$taskExpected = (@('propext', 'Classical.choice', 'Quot.sound') | Sort-Object) -join ','
$taskSeen = @{}
foreach ($taskReport in $taskReports) {
  $taskAxioms = @($taskReport.Groups['axioms'].Value -split ',' |
    ForEach-Object { $_.Trim() } | Where-Object { $_ } | Sort-Object)
  foreach ($taskAxiom in $taskAxioms) {
    if ($taskAxiom -notin @('propext', 'Classical.choice', 'Quot.sound')) {
      throw ('Unapproved axiom: ' + $taskAxiom)
    }
  }
  $taskSeen[$taskReport.Groups['decl'].Value] = $taskAxioms -join ','
}
$taskRequired = @('Erdos252.erdos_252',
  'Erdos252.Generalizations.irrational_cantor_iff',
  'Erdos252.Generalizations.irrational_joint_product_series_iff',
  'Erdos252.Generalizations.irrational_general_denominator',
  'Erdos252.Generalizations.irrational_corrected_sigma_factorial',
  'Erdos252.Generalizations.weighted_tail_obstruction',
  'GeneralizationsAudit.joint_statement',
  'GeneralizationsAudit.arbitrary_denominator_statement')
foreach ($taskDeclaration in $taskRequired) {
  if ($taskSeen[$taskDeclaration] -ne $taskExpected) {
    throw ('Missing or unexpected axiom report: ' + $taskDeclaration)
  }
}
Write-Output 'PASS explicit statement and axiom audits'

Invoke-Check 'kernel' (Join-Path $LeanBin 'leanchecker.exe') `
  @('--fresh', '--verbose', 'Generalizations.Audit')
foreach ($taskFile in $taskHashes.Keys) {
  if ((Get-FileHash -LiteralPath (Join-Path $taskRoot $taskFile)).Hash -ne $taskHashes[$taskFile]) {
    throw ('Source changed during verification: ' + $taskFile)
  }
}
[pscustomobject]@{
  status = 'PASS'
  startedUtc = $taskStarted.ToString('o')
  completedUtc = [DateTime]::UtcNow.ToString('o')
  sourceHashes = $taskHashes
  freshModules = $taskModules
  axiomReports = $taskSeen
  kernelModule = 'Generalizations.Audit'
} | ConvertTo-Json -Depth 5 |
  Out-File -LiteralPath (Join-Path $taskFresh 'receipt.json') -Encoding UTF8
Write-Output ('ALL CHECKS PASS: ' + (Join-Path $taskFresh 'receipt.json'))
