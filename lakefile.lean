import Lake
open Lake DSL System

require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "44d9c8a3b89bfe633c6e519bb4f142724be637b8"
require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "4cdea120ba132ba0cb817e7fd516a967f1148752"

package veil

-- Paths and URLs for SMT solvers
def z3.baseUrl := "https://github.com/Z3Prover/z3/releases/download"
def z3.version := "4.14.0"
def z3.arch := if System.Platform.target.startsWith "x86_64" then "x64" else "arm64"
def z3.platform :=
  if System.Platform.isWindows then "win"
  else if System.Platform.isOSX then "osx-13.7.2"
  else "glibc-2.34"
def z3.target := s!"{arch}-{platform}"
def z3.fullName := s!"z3-{version}-{z3.target}"
-- https://github.com/Z3Prover/z3/releases/download/z3-4.14.0/z3-4.14.0-arm64-osx-13.7.2.zip
def z3.url := s!"{baseUrl}/z3-{version}/{fullName}.zip"


def cvc5.baseUrl := "https://github.com/cvc5/cvc5/releases/download"
def cvc5.version := "1.2.1"
def cvc5.os :=
  if System.Platform.isWindows then "Win64"
  else if System.Platform.isOSX then "macOS"
  else "Linux"
def cvc5.arch := if System.Platform.target.startsWith "x86_64" then "x86_64" else "arm64"
def cvc5.target := s!"{os}-{arch}-static"
def cvc5.fullName := s!"cvc5-{cvc5.target}"
-- https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-macOS-arm64-static.zip
def cvc5.url := s!"{baseUrl}/cvc5-{version}/{fullName}.zip"

inductive Solver
| z3
| cvc5

instance : ToString Solver where
  toString := fun
    | Solver.z3 => "z3"
    | Solver.cvc5 => "cvc5"

def Solver.fullName (solver : Solver) : String :=
  match solver with
  | Solver.z3 => z3.fullName
  | Solver.cvc5 => cvc5.fullName

def Solver.url (solver : Solver) : String :=
  match solver with
  | Solver.z3 => z3.url
  | Solver.cvc5 => cvc5.url

-- Code to download SMT solvers

def Lake.unzip (file : FilePath) (dir : FilePath) : LogIO PUnit := do
  IO.FS.createDirAll dir
  proc (quiet := true) {
    cmd := "unzip"
    args := #["-d", dir.toString, file.toString]
  }

def Lake.copyFile (src : FilePath) (dst : FilePath) : LogIO PUnit := do
  proc (quiet := true) {
    cmd := "cp"
    args := #[src.toString, dst.toString]
  }

-- Modelled after https://github.com/abdoo8080/lean-cvc5/blob/6ab43688cff28aaf5096fb153e3dd89014bf4410/lakefile.lean#L62
def downloadSolver (solver : Solver) : FetchM Unit := do
 if let some pkg ← findPackage? _package.name then
    let solverPath := pkg.buildDir / s!"{solver}"
    if ← solverPath.pathExists then
      logInfo s!"{solver} already exists at {solverPath}"
      return
    let zipPath := solverPath.addExtension "zip"
    logInfo s!"Downloading {solver} from {solver.url}"
    download solver.url zipPath
    let extractedPath := pkg.buildDir / solver.fullName
    if ← extractedPath.pathExists then
      -- logInfo s!"Removing existing directory {extractedPath}"
      IO.FS.removeDirAll extractedPath
    -- logInfo s!"Unzipping {zipPath} into {pkg.buildDir}"
    unzip zipPath pkg.buildDir
    let binPath := extractedPath/ "bin" / s!"{solver}"
    copyFile binPath solverPath
    logInfo s!"{solver} is now at {solverPath}"
    IO.FS.removeFile zipPath
    IO.FS.removeDirAll extractedPath

-- Code to download Python `uv`

def uv.version := "0.6.2"
def uv.url := s!"https://astral.sh/uv/{uv.version}/install.sh"

-- curl -LsSf https://astral.sh/uv/install.sh | env UV_UNMANAGED_INSTALL="/custom/path" sh
def downloadPythonUv : FetchM Unit := do
 if let some pkg ← findPackage? _package.name then
    let uvShPath := pkg.buildDir / "install-uv.sh"
    let uvPath := pkg.buildDir / "uv"
    if ← uvPath.pathExists then
      logInfo s!"`uv` already exists at {uvPath}"
      return
    logInfo s!"Downloading `uv` from {uv.url} to {uvShPath}"
    download uv.url uvShPath
    proc {
      cmd := "env"
      args := #[s!"UV_UNMANAGED_INSTALL={pkg.buildDir}", "sh", uvShPath.toString]
    }
    logInfo s!"`uv` is now at {uvPath}"
    IO.FS.removeFile uvShPath

def downloadAllDeps : FetchM (BuildJob Unit) := do
  downloadSolver Solver.z3
  downloadSolver Solver.cvc5
  downloadPythonUv
  -- FIXME: I suspect this is not the right way to do this
  return BuildJob.nil

script downloadDependencies do
  let ws ← getWorkspace
  let args := ws.lakeArgs?.getD #[]
  let v := Verbosity.normal
  let v := if args.contains "-q" || args.contains "--quiet" then Verbosity.quiet else v
  let v := if args.contains "-v" || args.contains "--verbose" then Verbosity.verbose else v
  let exitCode ← LoggerIO.toBaseIO (minLv := v.minLogLv) <| ws.runFetchM do
    if let some _pkg ← findPackage? _package.name then
      let _ ← downloadAllDeps
      return 0
    else
      logError s!"package {_package.name} not found in workspace"
      return 1
  return ⟨exitCode.getD 1⟩

target downloadDeps : Unit := downloadAllDeps

@[default_target]
lean_lib «Veil» {
  globs := #[`Veil, .submodules `Veil, .submodules `Test]
  extraDepTargets := #[``downloadDeps]
}

lean_lib Examples {
  globs := #[.submodules `Examples]
}
