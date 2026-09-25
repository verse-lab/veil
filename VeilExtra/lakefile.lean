import Lake
open Lake DSL

require veil from ".."
require cslib from git "https://github.com/leanprover/cslib.git" @ "v4.32.0"

package VeilExtra

@[default_target]
lean_lib VeilExtra where
  globs := #[`VeilExtra, .submodules `VeilExtra]
