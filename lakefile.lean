import Lake
open Lake DSL

package «Veil» where

@[default_target]
lean_lib «Veil» {
  globs := #[.submodules `Veil]
}

-- @[default_target]
lean_lib Examples {
  globs := #[.submodules `Examples]
}

@[default_target]
lean_lib Test {
  globs := #[.submodules `Test]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"
require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "fa3040aa203ea9d88ae958fab0fca8284c3640de"
require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "213932fcac9c7757625cb917427d95897ea5fd1e"
require Duper from git "https://github.com/leanprover-community/duper.git" @ "a41cc06670aee9d4762a12a11574532c4077f52f"
