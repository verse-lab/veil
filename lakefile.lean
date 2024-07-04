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
  globs := #[.submodules `Examples]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.9.0"
require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "542821345b1e8eb8e244dacafa96d677d0a55340"
require Duper from git "https://github.com/dranov/duper.git" @ "bump-v4.9.0"

@[default_target]
lean_exe «lean-sts» where
  root := `Main
