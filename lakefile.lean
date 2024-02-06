import Lake
open Lake DSL

package «lean-sts» where
  -- add package configuration options here

lean_lib «LeanSts» where
  -- add library configuration options here

lean_lib «Examples» where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.6.0-rc1"

@[default_target]
lean_exe «lean-sts» where
  root := `Main
