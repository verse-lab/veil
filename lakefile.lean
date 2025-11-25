import Lake
open Lake DSL System

require smt from git "https://github.com/dranov/lean-smt.git" @ "veil-2.0"
require Loom from git "https://github.com/verse-lab/loom-dev.git" @ "extract-list"

package veil

@[default_target]
lean_lib «Veil» {
  globs := #[`Veil, .submodules `Veil]
  -- precompileModules := true
}

@[default_target, test_driver]
lean_lib Test {
  globs := #[Glob.submodules `Test]
}

lean_lib Examples {
  globs := #[.submodules `Examples]
}
