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

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"
require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "0f5f39a0336e36ae4ba8ab45b27865ebd9f8f025"
require Duper from git "https://github.com/leanprover-community/duper.git" @ "f5cb3a2e49766ec0c353669b840b86f4347816aa"

@[default_target]
lean_exe «lean-sts» where
  root := `Main
