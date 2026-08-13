import Lake
open Lake DSL System

require smt from git "https://github.com/verse-lab/lean-smt.git" @ "v4.32.0-veil-no-mathlib"
require Loom from git "https://github.com/verse-lab/loom.git" @ "v4.32.0-for-veil"

package veil where
  preferReleaseBuild := true
  buildArchive? := .none
  releaseRepo := "https://github.com/verse-lab/veil"

-- Widget build configuration (adapted from ProofWidgets)
def widgetDir : FilePath := "widget"

nonrec def Lake.Package.widgetDir (pkg : Package) : FilePath :=
  pkg.dir / widgetDir

def Lake.Package.runNpmCommand (pkg : Package) (args : Array String) : LogIO Unit :=
  -- Running `cmd := "npm.cmd"` directly fails on Windows sometimes
  -- so run in PowerShell instead
  if Platform.isWindows then
    proc {
      cmd := "powershell"
      args := #["-Command", "npm.cmd"] ++ args
      cwd := some pkg.widgetDir
    } (quiet := true)
  else
    proc {
      cmd := "npm"
      args
      cwd := some pkg.widgetDir
    } (quiet := true)

input_file widgetPackageJson where
  path := widgetDir / "package.json"
  text := true

/-- Target to update `package-lock.json` whenever `package.json` has changed. -/
target widgetPackageLock pkg : FilePath := do
  let packageFile ← widgetPackageJson.fetch
  let packageLockFile := pkg.widgetDir / "package-lock.json"
  buildFileAfterDep (text := true) packageLockFile packageFile fun _srcFile => do
    pkg.runNpmCommand #["install"]

input_file widgetRollupConfig where
  path := widgetDir / "rollup.config.js"
  text := true

input_file widgetTsconfig where
  path := widgetDir / "tsconfig.json"
  text := true

/-- The TypeScript widget modules in `widget/src`. -/
input_dir widgetJsSrcs where
  path := widgetDir / "src"
  filter := .extension <| .mem #["ts", "tsx", "js", "jsx"]
  text := true

/-- Target to build all widget modules from `widgetJsSrcs`. -/
def widgetJsAllTarget (pkg : Package) (isDev : Bool) : FetchM (Job Unit) := do
  let srcs ← widgetJsSrcs.fetch
  let rollupConfig ← widgetRollupConfig.fetch
  let tsconfig ← widgetTsconfig.fetch
  let widgetPackageLock ← widgetPackageLock.fetch
  /- `widgetJsAll` is built via `needs`,
  and Lake's default build order is `needs -> cloud release -> main build`.
  We must instead ensure that the cloud release is fetched first
  so that this target does not build from scratch unnecessarily.
  `afterBuildCacheAsync` guarantees this. -/
  pkg.afterBuildCacheAsync do
  srcs.bindM (sync := true) fun _ =>
  rollupConfig.bindM (sync := true) fun _ =>
  tsconfig.bindM (sync := true) fun _ =>
  widgetPackageLock.mapM fun _ => do
    let traceFile := pkg.buildDir / "js" / "lake.trace"
    buildUnlessUpToDate traceFile (← getTrace) traceFile do
      if let some msg := get_config? errorOnBuild then
        error msg
      /- Ensure that NPM modules are installed before building TypeScript,
       *if* we are building Typescript.
       This only runs when some TypeScript needs building. -/
      pkg.runNpmCommand #["clean-install"]
      pkg.runNpmCommand #["run", if isDev then "build-dev" else "build"]

target widgetJsAll pkg : Unit :=
  widgetJsAllTarget pkg (isDev := false)

target widgetJsAllDev pkg : Unit :=
  widgetJsAllTarget pkg (isDev := true)

@[default_target]
lean_lib «Veil» {
  globs := #[`Veil, .submodules `Veil]
  -- precompileModules := true
  needs := #[widgetJsAll]
}

@[default_target, test_driver]
lean_lib VeilTest {
  globs := #[Glob.submodules `VeilTest]
  leanOptions := #[⟨`weak.veil.smt.trust, false⟩]
}

lean_lib Examples {
  globs := #[.submodules `Examples]
}

/--
Run performance tests with timeout enforcement.

USAGE:
  lake script run perftest

Runs all `.lean` files under `VeilTest/Performance/` and checks that each
completes within the timeout specified in its accompanying `.timeout` file
(in seconds). If no `.timeout` file exists, a default of 20 seconds is used.

Example `.timeout` file contents:
```
20
```
-/
script perftest do
  let perfDir : FilePath := "VeilTest" / "Performance"
  if !(← perfDir.pathExists) then
    IO.println "No VeilTest/Performance/ directory found."
    return 1
  let entries ← perfDir.readDir
  let tests := entries.filterMap fun e =>
    if e.path.extension = some "lean" then some e.path else none
  if tests.isEmpty then
    IO.println "No performance tests found in VeilTest/Performance/."
    return 0
  let lean ← getLean
  let env ← getAugmentedEnv
  let mut allPassed := true
  for test in tests do
    let timeoutSec ← readTimeout test
    IO.println s!"Running {test} (timeout: {timeoutSec}s) ..."
    let (timedOut, elapsedMs, exitCode, stdout, stderr) ←
      runWithTimeout lean.toString #[test.toString] env (timeoutSec * 1000)
    let elapsedSec := elapsedMs / 1000
    if timedOut then
      IO.println s!"  TIMEOUT after {elapsedSec}s (limit: {timeoutSec}s)"
      allPassed := false
    else if exitCode ≠ 0 then
      IO.println s!"  FAILED (exit code {exitCode}, {elapsedSec}s)"
      if !stderr.isEmpty then
        IO.println s!"  Stderr: {stderr.trimAscii}"
      allPassed := false
    else
      IO.println s!"  PASSED ({elapsedSec}s)"
      if !stdout.isEmpty then
        for line in stdout.trimAscii.toString.splitOn "\n" do
          IO.println s!"    {line}"
  return if allPassed then 0 else 1
where
  readTimeout (test : FilePath) : IO Nat := do
    let timeoutFile := test.withExtension "timeout"
    if ← timeoutFile.pathExists then
      let content ← IO.FS.readFile timeoutFile
      return content.trimAscii.toNat?.getD 20
    else return 120
  runWithTimeout (cmd : String) (args : Array String)
      (env : Array (String × Option String)) (timeoutMs : Nat)
      : IO (Bool × Nat × UInt32 × String × String) := do
    IO.println s!"  Executing: {cmd} {String.intercalate " " args.toList}"
    let child ← IO.Process.spawn {
      cmd := cmd
      args := args
      env := env
      stdout := .piped
      stderr := .piped
    }
    -- Read stdout/stderr in background tasks to avoid pipe deadlock
    let stdoutTask ← IO.asTask child.stdout.readToEnd
    let stderrTask ← IO.asTask child.stderr.readToEnd
    -- Track process completion via shared flag
    let doneRef ← IO.mkRef false
    let exitCodeRef ← IO.mkRef (0 : UInt32)
    let _ ← IO.asTask do
      let code ← child.wait
      exitCodeRef.set code
      doneRef.set true
    -- Poll until done or timeout
    let startTime ← IO.monoMsNow
    let mut timedOut := false
    repeat
      if ← doneRef.get then break
      IO.sleep 1000
      let elapsed := (← IO.monoMsNow) - startTime
      if elapsed > timeoutMs then
        timedOut := true
        child.kill
        break
    let exitCode ← exitCodeRef.get
    let stdout ← IO.ofExcept stdoutTask.get
    let stderr ← IO.ofExcept stderrTask.get
    let elapsed := (← IO.monoMsNow) - startTime
    return (timedOut, elapsed, exitCode, stdout, stderr)
