import Veil.Frontend.DSL.Module.Util.ForModelChecker

open Veil.ModelChecker.Compilation

run_cmd do
  let cases := #[
    ("-- λ\nimport /- keep -/ Veil\nimport Lean\n\ndef text := \"import Veil\"",
     "-- λ\nimport /- keep -/ Veil.Core\nimport Lean\n\ndef text := \"import Veil\""),
    ("/-\nimport Veil\n-/\nimport\n  «Veil»\n\n#check Nat",
     "/-\nimport Veil\n-/\nimport\n  Veil.Core\n\n#check Nat"),
    ("module\npublic import Veil\nmeta import Veil.DSL\nimport all Veil.Frontend.DSL.Base\n",
     "module\npublic import Veil.Core\nmeta import Veil.Core\nimport all Veil.Core\n"),
    ("import Veil.Core\nimport Veil.Util.Permutations\n#check Nat",
     "import Veil.Core\nimport Veil.Util.Permutations\n#check Nat"),
    ("import Lean\n#check Nat",
     "import Lean\n\nimport Veil.Core\n#check Nat")
  ]
  for (src, expected) in cases do
    let (header, bodyPos) ← prepareCoreHeader src
    let actual := header ++ String.Pos.Raw.extract src bodyPos src.rawEndPos
    unless actual == expected do
      throwError "Incorrect native import rewrite:\n{actual}\nExpected:\n{expected}"
