import Lake
open Lake DSL

require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "44d9c8a3b89bfe633c6e519bb4f142724be637b8"
require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "4cdea120ba132ba0cb817e7fd516a967f1148752"

package veil

@[default_target]
lean_lib «Veil» {
  globs := #[.submodules `Veil, .submodules `Test, .submodules `Library]
}

lean_lib Examples {
  globs := #[.submodules `Examples]
}
