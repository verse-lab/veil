import Lake
open Lake DSL

def libcpp : String :=
  if System.Platform.isWindows then "libstdc++-6.dll"
  else if System.Platform.isOSX then "libc++.dylib"
  else "libstdc++.so.6"

package «lean-sts» where
  moreLeanArgs := #[s!"--load-dynlib={libcpp}"]
  moreGlobalServerArgs := #[s!"--load-dynlib={libcpp}"]
  moreLinkArgs :=
    if System.Platform.isOSX || System.Platform.isWindows then #[]
    else #["-L/usr/lib/x86_64-linux-gnu", "/usr/lib/x86_64-linux-gnu/libstdc++.so.6"]

@[default_target]
lean_lib «LeanSts» where
  -- add library configuration options here

@[default_target]
lean_lib Examples {
  globs := #[.submodules `Examples]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"
require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "3fe4c17089b468490d654a135621b884848e0c05"
require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "82a65848db999cbca865f278b52649f77bea61a5"
require Duper from git "https://github.com/dranov/duper.git" @ "bump-v4.11.0"
