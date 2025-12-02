import Lake
open Lake DSL System

require smt from git "https://github.com/dranov/lean-smt.git" @ "veil-2.0-v4.25.2"
require Loom from git "https://github.com/verse-lab/loom-dev.git" @ "extract-list-v4.25.2"

package veil

/-- The TypeScript widget modules in `Core/UI`. -/
input_dir widgetJsSrcs where
  path := "." / "Veil" / "Core" / "UI" / "Verifier"
  filter := .extension <| .mem #["ts", "tsx", "js", "jsx"]
  text := true


@[default_target]
lean_lib «Veil» {
  globs := #[`Veil, .submodules `Veil]
  -- precompileModules := true
  needs := #[widgetJsSrcs]

}

@[default_target, test_driver]
lean_lib Test {
  globs := #[Glob.submodules `Test]
}

lean_lib Examples {
  globs := #[.submodules `Examples]
}
