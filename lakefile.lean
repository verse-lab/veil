import Lake
open Lake DSL

def libcpp : String :=
  if System.Platform.isWindows then "libstdc++-6.dll"
  else if System.Platform.isOSX then "libc++.dylib"
  else "libstdc++.so.6"

package «lean-sts» where
  moreLeanArgs := #[s!"--load-dynlib={libcpp}"]
  moreGlobalServerArgs := #[s!"--load-dynlib={libcpp}"]
  -- TODO: make this cross-platform
  moreLinkArgs := #["-L/usr/lib/x86_64-linux-gnu", "/usr/lib/x86_64-linux-gnu/libstdc++.so.6"]


@[default_target]
lean_lib «LeanSts» where
  -- add library configuration options here

@[default_target]
lean_lib Examples {
  globs := #[.submodules `Examples]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.9.0"
require auto from git "https://github.com/dranov/lean-auto.git" @ "dranov"
require smt from git "https://github.com/dranov/lean-smt.git" @ "dranov"
require Duper from git "https://github.com/leanprover-community/duper.git" @ "d53f474c91d39d49d0d30fa8d8deca51c4559690"

@[default_target]
lean_exe «lean-sts» where
  root := `Main
