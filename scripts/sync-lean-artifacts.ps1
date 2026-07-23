[CmdletBinding()]
param(
  [string]$Owner = '',
  [string]$Repository = '',
  [long]$RunId = 0,
  [string]$Workflow = 'lean_action_ci.yml',
  [string]$Branch = 'main'
)

Set-StrictMode -Version Latest

$artifactToken = $null
$temporaryRoot = $null
$syncBaseFull = $null

try {
  $repositoryRoot = ((& git rev-parse --show-toplevel 2>$null) -join '').Trim()
  if ($LASTEXITCODE -ne 0 -or [string]::IsNullOrWhiteSpace($repositoryRoot)) {
    throw 'Run this script from inside the Ringel Git repository.'
  }
  $repositoryRoot = [IO.Path]::GetFullPath($repositoryRoot)

  if ([string]::IsNullOrWhiteSpace($Owner) -or
      [string]::IsNullOrWhiteSpace($Repository)) {
    $remoteUrl = ((& git -C $repositoryRoot remote get-url origin 2>$null) -join '').Trim()
    if ($LASTEXITCODE -ne 0 -or
        $remoteUrl -notmatch 'github\.com[/:](?<owner>[^/]+)/(?<repo>[^/]+)$') {
      throw 'Could not infer GitHub owner/repository from the origin remote.'
    }
    if ([string]::IsNullOrWhiteSpace($Owner)) {
      $Owner = $Matches.owner
    }
    if ([string]::IsNullOrWhiteSpace($Repository)) {
      $Repository = $Matches.repo
      if ($Repository.EndsWith('.git', [StringComparison]::OrdinalIgnoreCase)) {
        $Repository = $Repository.Substring(0, $Repository.Length - 4)
      }
    }
  }

  $artifactToken = $env:GITHUB_TOKEN
  if ([string]::IsNullOrWhiteSpace($artifactToken)) {
    $credentialRequest = "protocol=https`nhost=github.com`n`n"
    $credentialLines = @($credentialRequest | git credential fill 2>$null)
    $passwordLine = $credentialLines |
      Where-Object { $_ -like 'password=*' } |
      Select-Object -First 1
    if ($LASTEXITCODE -ne 0 -or -not $passwordLine) {
      throw 'No GitHub token found in GITHUB_TOKEN or the Git credential helper.'
    }
    $artifactToken = $passwordLine.Substring(9)
  }

  $githubHeaders = @{
    Authorization = "Bearer $artifactToken"
    Accept = 'application/vnd.github+json'
    'X-GitHub-Api-Version' = '2022-11-28'
    'User-Agent' = 'Ringel-Lean-artifact-sync'
  }
  $apiBase = 'https://api.github.com/repos/{0}/{1}' -f
    [Uri]::EscapeDataString($Owner), [Uri]::EscapeDataString($Repository)

  if ($RunId -eq 0) {
    $runsUri = '{0}/actions/workflows/{1}/runs?branch={2}&status=success&per_page=1' -f
      $apiBase,
      [Uri]::EscapeDataString($Workflow),
      [Uri]::EscapeDataString($Branch)
    $runsResponse = Invoke-RestMethod -Uri $runsUri -Headers $githubHeaders
    $workflowRuns = @($runsResponse.workflow_runs)
    if ($workflowRuns.Count -eq 0) {
      throw "No successful $Workflow run found on branch $Branch."
    }
    $workflowRun = $workflowRuns[0]
  } else {
    $workflowRun = Invoke-RestMethod `
      -Uri "$apiBase/actions/runs/$RunId" `
      -Headers $githubHeaders
    if ($workflowRun.status -ne 'completed') {
      throw "Workflow run $RunId is not complete."
    }
  }

  $artifactResponse = Invoke-RestMethod `
    -Uri "$apiBase/actions/runs/$($workflowRun.id)/artifacts?per_page=100" `
    -Headers $githubHeaders
  $artifacts = @(
    $artifactResponse.artifacts |
      Where-Object { -not $_.expired -and $_.name -like 'ringel-lean-*' } |
      Sort-Object created_at -Descending
  )
  if ($artifacts.Count -eq 0) {
    throw "Workflow run $($workflowRun.id) has no unexpired Ringel Lean artifact."
  }
  $artifact = $artifacts[0]

  $syncBase = Join-Path $repositoryRoot '.lake\artifact-sync'
  $syncBaseFull = [IO.Path]::GetFullPath($syncBase).TrimEnd(
    [IO.Path]::DirectorySeparatorChar,
    [IO.Path]::AltDirectorySeparatorChar
  ) + [IO.Path]::DirectorySeparatorChar
  New-Item -ItemType Directory -Path $syncBaseFull -Force | Out-Null

  $temporaryRoot = Join-Path $syncBaseFull ([guid]::NewGuid().ToString('N'))
  $temporaryFull = [IO.Path]::GetFullPath($temporaryRoot)
  if (-not $temporaryFull.StartsWith(
      $syncBaseFull, [StringComparison]::OrdinalIgnoreCase)) {
    throw "Unsafe temporary path: $temporaryFull"
  }
  New-Item -ItemType Directory -Path $temporaryFull | Out-Null

  $archivePath = Join-Path $temporaryFull 'artifact.zip'
  Invoke-WebRequest `
    -Uri $artifact.archive_download_url `
    -Headers $githubHeaders `
    -OutFile $archivePath `
    -MaximumRedirection 10

  if ($artifact.digest -match '^sha256:(?<digest>[0-9a-fA-F]{64})$') {
    $actualDigest = (Get-FileHash -LiteralPath $archivePath -Algorithm SHA256).Hash
    if ($actualDigest -ne $Matches.digest) {
      throw "Artifact digest mismatch: expected $($Matches.digest), got $actualDigest."
    }
  }

  Add-Type -AssemblyName System.IO.Compression.FileSystem
  $stagingRoot = Join-Path $temporaryFull 'files'
  New-Item -ItemType Directory -Path $stagingRoot | Out-Null
  $stagingFull = [IO.Path]::GetFullPath($stagingRoot).TrimEnd(
    [IO.Path]::DirectorySeparatorChar,
    [IO.Path]::AltDirectorySeparatorChar
  ) + [IO.Path]::DirectorySeparatorChar
  $archive = [IO.Compression.ZipFile]::OpenRead($archivePath)
  try {
    foreach ($entry in $archive.Entries) {
      if ([string]::IsNullOrEmpty($entry.Name)) {
        continue
      }
      $entryPath = $entry.FullName.Replace(
        '/', [IO.Path]::DirectorySeparatorChar
      )
      if ([IO.Path]::IsPathRooted($entryPath)) {
        throw "Unsafe rooted artifact entry: $($entry.FullName)"
      }
      $destinationPath = [IO.Path]::GetFullPath(
        (Join-Path $stagingFull $entryPath)
      )
      if (-not $destinationPath.StartsWith(
          $stagingFull, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Unsafe artifact entry: $($entry.FullName)"
      }
      $destinationDirectory = Split-Path -Parent $destinationPath
      New-Item -ItemType Directory -Path $destinationDirectory -Force | Out-Null
      [IO.Compression.ZipFileExtensions]::ExtractToFile(
        $entry, $destinationPath, $true
      )
    }
  } finally {
    $archive.Dispose()
  }

  $buildRootCandidates = @(
    $stagingFull,
    (Join-Path $stagingFull '.lake\build'),
    (Join-Path $stagingFull 'build')
  )
  $sourceRoot = $null
  foreach ($candidate in $buildRootCandidates) {
    if (Test-Path -LiteralPath (Join-Path $candidate 'lib\lean\Ringel')) {
      $sourceRoot = $candidate
      break
    }
  }

  if ($sourceRoot) {
    $artifactLayout = 'full-build'
    $targetRoot = Join-Path $repositoryRoot '.lake\build'
  } else {
    $legacyOleans = @(
      Get-ChildItem -LiteralPath $stagingFull -Filter '*.olean' -File
    )
    if ($legacyOleans.Count -eq 0) {
      throw 'Artifact contains neither a full Lake build nor legacy Lean files.'
    }
    $artifactLayout = 'lean-only'
    $sourceRoot = $stagingFull
    $targetRoot = Join-Path $repositoryRoot '.lake\build\lib\lean\Ringel'
  }

  $sourceFull = [IO.Path]::GetFullPath($sourceRoot).TrimEnd(
    [IO.Path]::DirectorySeparatorChar,
    [IO.Path]::AltDirectorySeparatorChar
  ) + [IO.Path]::DirectorySeparatorChar
  $stagedFiles = @(Get-ChildItem -LiteralPath $sourceFull -Recurse -File)
  $oleanCount = @($stagedFiles | Where-Object Extension -eq '.olean').Count
  $ileanCount = @($stagedFiles | Where-Object Extension -eq '.ilean').Count
  if ($oleanCount -eq 0 -or $oleanCount -ne $ileanCount) {
    throw "Invalid Lean artifact: $oleanCount .olean and $ileanCount .ilean files."
  }

  $targetFull = [IO.Path]::GetFullPath($targetRoot)
  $allowedTarget = [IO.Path]::GetFullPath(
    (Join-Path $repositoryRoot '.lake\build')
  ).TrimEnd(
    [IO.Path]::DirectorySeparatorChar,
    [IO.Path]::AltDirectorySeparatorChar
  ) + [IO.Path]::DirectorySeparatorChar
  $targetWithSeparator = $targetFull.TrimEnd(
    [IO.Path]::DirectorySeparatorChar,
    [IO.Path]::AltDirectorySeparatorChar
  ) + [IO.Path]::DirectorySeparatorChar
  if (-not $targetWithSeparator.StartsWith(
      $allowedTarget, [StringComparison]::OrdinalIgnoreCase)) {
    throw "Unsafe Lean artifact target: $targetFull"
  }
  New-Item -ItemType Directory -Path $targetFull -Force | Out-Null

  $syncTime = [DateTime]::UtcNow.AddSeconds(1)
  $utf8NoBom = [Text.UTF8Encoding]::new($false)
  foreach ($sourceFile in $stagedFiles) {
    $relativePath = [IO.Path]::GetRelativePath(
      $sourceFull, $sourceFile.FullName
    )
    $destinationPath = [IO.Path]::GetFullPath(
      (Join-Path $targetFull $relativePath)
    )
    if (-not $destinationPath.StartsWith(
        $targetWithSeparator, [StringComparison]::OrdinalIgnoreCase)) {
      throw "Unsafe Lean artifact destination: $destinationPath"
    }
    $destinationDirectory = Split-Path -Parent $destinationPath
    New-Item -ItemType Directory -Path $destinationDirectory -Force | Out-Null
    Copy-Item -LiteralPath $sourceFile.FullName -Destination $destinationPath -Force

    if ($sourceFile.Extension -eq '.trace') {
      $trace = Get-Content -Raw -LiteralPath $destinationPath | ConvertFrom-Json
      if ($trace.schemaVersion -and $trace.depHash -and $trace.outputs) {
        $portableTrace = [ordered]@{
          schemaVersion = $trace.schemaVersion
          depHash = $trace.depHash
          outputs = $trace.outputs
        }
        $portableJson = $portableTrace | ConvertTo-Json -Depth 50 -Compress
        [IO.File]::WriteAllText(
          $destinationPath, $portableJson + "`n", $utf8NoBom
        )
      }
    }
    (Get-Item -LiteralPath $destinationPath).LastWriteTimeUtc = $syncTime
  }

  $currentHead = ((& git -C $repositoryRoot rev-parse HEAD) -join '').Trim()
  $sourceCompatible = $currentHead -eq $workflowRun.head_sha
  if (-not $sourceCompatible) {
    & git -C $repositoryRoot cat-file -e "$($workflowRun.head_sha)^{commit}" 2>$null
    if ($LASTEXITCODE -eq 0) {
      & git -C $repositoryRoot diff --quiet `
        "$($workflowRun.head_sha)..$currentHead" -- `
        '*.lean' lean-toolchain lakefile.toml lake-manifest.json
      $sourceCompatible = $LASTEXITCODE -eq 0
    }
  }
  if (-not $sourceCompatible) {
    Write-Warning (
      "Artifact commit $($workflowRun.head_sha) differs in Lean-sensitive files; " +
      'edited modules may need a newer GitHub build.'
    )
  }

  [PSCustomObject]@{
    RunId = $workflowRun.id
    Commit = $workflowRun.head_sha
    Artifact = $artifact.name
    Olean = $oleanCount
    Ilean = $ileanCount
    Target = $targetFull
    Layout = $artifactLayout
    SourceCompatible = $sourceCompatible
  }
} finally {
  $artifactToken = $null
  if ($temporaryRoot -and $syncBaseFull -and
      (Test-Path -LiteralPath $temporaryRoot)) {
    $temporaryFull = [IO.Path]::GetFullPath($temporaryRoot)
    if ($temporaryFull.StartsWith(
        $syncBaseFull, [StringComparison]::OrdinalIgnoreCase)) {
      Remove-Item -LiteralPath $temporaryFull -Recurse -Force
    }
  }
}
