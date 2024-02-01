import Lake
open Lake DSL

package «lean-sts» where
  -- add package configuration options here

lean_lib «LeanSts» where
  -- add library configuration options here

lean_lib «Examples» where

@[default_target]
lean_exe «lean-sts» where
  root := `Main
