import Lake
open Lake DSL

package «lean-sts» where
  -- add package configuration options here

lean_lib «LeanSts» where
  -- add library configuration options here

lean_lib «Examples» where

require LSpec from git "https://github.com/lurk-lab/LSpec.git"

@[default_target]
lean_exe «lean-sts» where
  root := `Main
