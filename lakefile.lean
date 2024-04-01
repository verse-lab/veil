import Lake
open Lake DSL

package «lean-sts» where
  -- add package configuration options here
  -- moreLeanArgs := #[s!"--load-dynlib={nameToSharedLib "c++"}.1"]
  -- moreLinkArgs := #["-lstdc++"]
  -- moreGlobalServerArgs := #[s!"--load-dynlib={nameToSharedLib "c++"}.1"]

@[default_target]
lean_lib «LeanSts» where
  -- add library configuration options here

@[default_target]
lean_lib Examples {
  globs := #[.submodules "Examples"]
}
-- require smt from git "https://github.com/dranov/lean-smt.git"@"fix-link-error"
-- lean-smt includes mathlib
-- require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.4.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
require auto from git "https://github.com/dranov/lean-auto.git" @ "higher-order-debug"
require Duper from git "https://github.com/leanprover-community/duper.git" @ "v0.0.10"

@[default_target]
lean_exe «lean-sts» where
  root := `Main
