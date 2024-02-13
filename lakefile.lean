import Lake
open Lake DSL

package «lean-sts» where
  moreLeanArgs := #[s!"--load-dynlib={nameToSharedLib "c++"}.1"]
  -- add package configuration options here
  moreLinkArgs := #["-lstdc++"]
  moreGlobalServerArgs := #[s!"--load-dynlib={nameToSharedLib "c++"}.1"]

lean_lib «LeanSts» where
  -- add library configuration options here

lean_lib «Examples» where

-- require smt from git "https://github.com/dranov/lean-smt.git"@"fix-link-error"
-- lean-smt includes mathlib
-- require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.4.0"

require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.6.0-rc1"

@[default_target]
lean_exe «lean-sts» where
  root := `Main
