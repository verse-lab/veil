import Lake
open Lake DSL System

-- FIXME: change to "https://github.com/leanprover-community/lean-auto.git" once they bump to v4.16.0 upstream
require auto from git "https://github.com/dranov/lean-auto.git" @ "bump-v4.20.0-rc3"
require smt from git "https://github.com/dranov/lean-smt.git" @ "bump-v4.20.0-rc3"
require Loom from git "https://github.com/verse-lab/loom-dev.git" @ "master"

package veil

-- ## Dependencies
-- IMPORTANT: If you change any of these, also change `dependencies.toml`
def z3.version := "4.14.0"
def cvc5.version := "1.2.1"
def uv.version := "0.6.2"
-- Changes to this file trigger re-downloading dependencies
-- FIXME: changing one version triggers re-downloading ALL dependencies
def dependencyFile := "dependencies.toml"

def z3.baseUrl := "https://github.com/Z3Prover/z3/releases/download"
def z3.arch := if System.Platform.target.startsWith "x86_64" then "x64" else "arm64"
def z3.platform :=
  if System.Platform.isWindows then "win"
  else if System.Platform.isOSX then "osx-13.7.2"
  -- linux x64
  else if System.Platform.target.startsWith "x86_64" then "glibc-2.35"
  -- linux arm64
  else if System.Platform.target.startsWith "aarch64" then "glibc-2.34"
  else panic! s!"Unsupported platform: {System.Platform.target}"

def z3.target := s!"{arch}-{platform}"
def z3.fullName := s!"z3-{version}-{z3.target}"
-- https://github.com/Z3Prover/z3/releases/download/z3-4.14.0/z3-4.14.0-arm64-osx-13.7.2.zip
def z3.url := s!"{baseUrl}/z3-{version}/{fullName}.zip"

def cvc5.baseUrl := "https://github.com/cvc5/cvc5/releases/download"
def cvc5.os :=
  if System.Platform.isWindows then "Win64"
  else if System.Platform.isOSX then "macOS"
  else "Linux"
def cvc5.arch := if System.Platform.target.startsWith "x86_64" then "x86_64" else "arm64"
def cvc5.target := s!"{os}-{arch}-static"
def cvc5.fullName := s!"cvc5-{cvc5.target}"
-- https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-macOS-arm64-static.zip
def cvc5.url := s!"{baseUrl}/cvc5-{version}/{fullName}.zip"

def uv.url := s!"https://astral.sh/uv/{uv.version}/install.sh"

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

-- ## Code to download dependencies

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

-- curl -LsSf https://astral.sh/uv/install.sh | env UV_UNMANAGED_INSTALL="/custom/path" sh
def downloadPythonUv (pkg : Package) (oFile : FilePath) : JobM PUnit := do
  let uvShPath := pkg.buildDir / "install-uv.sh"
  logInfo s!"Downloading uv from {uv.url}"
  download uv.url uvShPath
  proc (quiet := true) {
    cmd := "env"
    args := #[s!"UV_UNMANAGED_INSTALL={pkg.buildDir}", "sh", uvShPath.toString]
  }
  if ← oFile.pathExists then
    logInfo s!"uv is now at {oFile}"
  else
    logError s!"Failed to download uv to {oFile}"
  IO.FS.removeFile uvShPath

-- Modelled after https://github.com/abdoo8080/lean-cvc5/blob/6ab43688cff28aaf5096fb153e3dd89014bf4410/lakefile.lean#L62
def downloadSolver (solver : Solver) (pkg : Package) (oFile : FilePath) : JobM PUnit := do
  let zipPath := (pkg.buildDir / s!"{solver}").addExtension "zip"
  logInfo s!"Downloading {solver} from {solver.url}"
  download solver.url zipPath
  let extractedPath := pkg.buildDir / solver.fullName
  if ← extractedPath.pathExists then
    IO.FS.removeDirAll extractedPath
  unzip zipPath pkg.buildDir
  let binPath := extractedPath/ "bin" / s!"{solver}"
  copyFile binPath oFile
  if ← oFile.pathExists then
    logInfo s!"{solver} is now at {oFile}"
  else
    logError s!"Failed to download {solver} to {oFile}"
  IO.FS.removeFile zipPath
  IO.FS.removeDirAll extractedPath

def downloadDependency (pkg : Package) (oFile : FilePath) (build : Package → FilePath → JobM PUnit) := do
  let lakefilePath := pkg.lakeDir / ".." / dependencyFile
  let srcJob ← inputTextFile lakefilePath
  buildFileAfterDep oFile srcJob fun _srcFile => build pkg oFile

target downloadDependencies pkg : Array FilePath := do
  let uv ← downloadDependency pkg (pkg.buildDir / "uv") downloadPythonUv
  let z3 ← downloadDependency pkg (pkg.buildDir / "z3") (downloadSolver Solver.z3)
  let cvc5 ← downloadDependency pkg (pkg.buildDir / "cvc5") (downloadSolver Solver.cvc5)
  return Job.collectArray #[uv, z3, cvc5]

@[default_target]
lean_lib «Veil» {
  globs := #[`Veil, .submodules `Veil]
  precompileModules := true
  extraDepTargets := #[``downloadDependencies]
}

@[default_target, test_driver]
lean_lib Test {
  globs := #[Glob.submodules `Test]
}

lean_lib Examples {
  globs := #[.submodules `Examples]
}
