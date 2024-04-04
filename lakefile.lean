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

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "main"
require Duper from git "https://github.com/leanprover-community/duper.git" @ "main"

@[default_target]
lean_exe «lean-sts» where
  root := `Main
