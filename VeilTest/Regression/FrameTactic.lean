module
public import Veil

-- Importing Veil alone must not register the tactic in ordinary Lean code.
open Lean Elab Command in
run_cmd do
  if (Parser.runParserCategory (← getEnv) `tactic "veil_frame").isOk then
    throwError "veil_frame is visible outside the Veil scope"

veil module FrameTactic

type node
immutable individual enabled : Bool
individual counter : Nat
relation live : node → Bool
individual history : List Nat
individual backup : Nat

after_init { counter := 0; live N := false; history := []; backup := 0 }
action write (n : node) {
  require counter = 0
  let m ← pick node
  require m = n
  live m := true
}
action reset { counter := 1 }
-- Copying a different field changes the destination even when both have the same type.
action restore { counter := backup }
transition keep { counter' = counter }
invariant [bound] enabled = true → counter ≤ 2
invariant [nested.zero] counter = 0
invariant [emptyLog] history = []
invariant [noLive] ¬ live N
-- The quantifier shadows the state field named counter.
invariant [logZeros] ∀ (counter : Nat), counter ∈ history → counter = 0

#gen_spec

-- Run the tactic on the same unsimplified public statements as a discharger.
-- Every positive example is separately accepted as a theorem by Lean.
open Lean Elab Command in
run_cmd do
  let mod ← getCurrentModule
  for (act, inv) in [(`write, `bound), (`write, `nested.zero), (`write, `emptyLog),
      (`reset, `noLive), (`restore, `logZeros)] do
    let vc ← mod.mkInvariantGoalVC (mkIdent act) (mkIdent inv) .wp
    elabCommand (← `(example $(vc.params)* : $(vc.statement) := by veil_frame))
  for (act, inv, style) in [(`write, `noLive, VCStyle.wp), (`reset, `nested.zero, .wp),
      (`restore, `nested.zero, .wp), (`initializer, `emptyLog, .wp), (`write, `doesNotThrow, .wp), (`keep, `emptyLog, .tr)] do
    let vc ← mod.mkInvariantGoalVC (mkIdent act) (mkIdent inv) style
    let succeeded ← liftTermElabM do
      let target ← vc.toVCStatement.type
      try
        discard <| mkFrameProof mod target
        return true
      catch _ => return false
    if succeeded then throwError "unexpected frame proof for {act}/{inv}"

end FrameTactic

veil module DirectFrameOnly

type node
type Bag
instantiate elems : TSet Bool Bag
individual flags : Bag
function lower : node → Nat
function upper : node → Nat

set_option veil.deferVCGeneration true
set_option veil.warnHybridFields false

after_init { flags := elems.empty; lower I := 0; upper I := 0 }
action insertFalse { flags := elems.insert false flags }
action setBoth (i : node) { lower i := 1; upper i := 1 }

invariant [onlyFalse] ∀ x : {x // x ∈ flags}, x.val = false
invariant [ordered] ∀ i : node, lower i ≤ upper i

#gen_spec

-- Both actions preserve both clauses. Direct framing succeeds only for the
-- disjoint pairs. The changed set or changed function needs a separate proof.
open Lean Elab Command in
run_cmd do
  discard <| (← getCurrentModule).ensureVerificationSpec (← getRef)
  let mgr ← Verifier.readVCManager
  for (name, shouldProve) in [(`insertFalse_ordered, true), (`setBoth_onlyFalse, true),
      (`insertFalse_onlyFalse, false), (`setBoth_ordered, false)] do
    let some vc := mgr.nodes.valuesArray.find? (·.name == name) | throwError "missing {name}"
    let #[frame, _] := vc.dischargers | throwError "expected a fallback for {name}"
    unless frame.id.name.toString.endsWith "_FRAME" do throwError "expected frame first"
    let _ ← frame.run
    match frame.resultPromise.result?.get with
    | some (.proven (some proof) ..) =>
      unless shouldProve && !proof.hasSorry do throwError "unexpected frame proof for {name}"
    | some (.unknown none _) => if shouldProve then throwError "frame declined {name}"
    | _ => throwError "unexpected worker result for {name}"

end DirectFrameOnly
