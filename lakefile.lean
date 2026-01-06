import Lake
open Lake DSL System

require smt from git "https://github.com/dranov/lean-smt.git" @ "veil-2.0-v4.25.2"
require Loom from git "https://github.com/verse-lab/loom-dev.git" @ "extract-list-v4.25.2"

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
lean_lib Test {
  globs := #[Glob.submodules `Test]
}

lean_lib Examples {
  globs := #[.submodules `Examples]
}
