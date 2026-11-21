module

public import Veil
open Lean Elab Command Meta Veil

set_option veil.violationIsError false

veil module WitnessReplay

immutable individual active : Bool
individual count : Nat
assumption [enabled] active = true
after_init { count := 1 }
action advance (k : Fin 5) {
  require k.val = 0 ∨ k.val = 2
  count := count + k.val
}
action twin { count := count + 2 }
invariant [zero] count = 0
#gen_spec

#guard_msgs (drop info, drop warning) in
#check_invariants

#guard_msgs (drop info) in
sat trace [wanted] {
  advance
  assert (count = 3)
  any action
}

#guard_msgs (drop info) in
unsat trace [unexpected] {
  advance
  assert (count = 3)
  any action
}

#guard_msgs (drop info) in
sat trace [initial] { assert (count = 1) }

private meta def expectCheck (what : String) (actual expected : WitnessCheck) : TermElabM Unit := do
  unless actual == expected do throwError "{what}: expected {repr expected}, got {repr actual}"

run_cmd do
  let mod ← getCurrentModule
  let results ← Verifier.waitFilteredSync (fun _ => true)
  let mut numChecked := 0
  for vc in results.vcs do
    let some model := vc.timing.dischargers.findSome? (fun d => match d.result with
      | some (.proven _ (some (.sat ms)) _) | some (.disproven (some (.sat ms)) _) => ms.findSome? id
      | _ => none) | continue
    match vc.metadata with
    | .trace md =>
      liftTermElabM do
        let w ← buildTraceFromModel model.raw mod md.numTransitions
        if md.numTransitions == 0 then
          let (_, q) ← mkTraceQuery mod (← `(traceSpec| assert ($(mkIdent `count):ident = 1)))
          expectCheck "initial assertion" (← q.check w) .checked
          let (_, empty) ← mkTraceQuery mod (← `(traceSpec|))
          expectCheck "non-initial state" (← empty.check { w with
            stateExprs := #[← Term.elabTermAndSynthesize (← `(⟨7⟩)) (some w.stateType)] }) .invalid
          expectCheck "trace theory" (← empty.check { w with
            theoryExpr := ← mkAppM ``Theory.mk #[mkConst ``Bool.false] }) .invalid
        else
          let (_, q) ← mkTraceQuery mod (← `(traceSpec|
            $(mkIdent `advance):ident
            assert ($(mkIdent `count):ident = 3)
            any action))
          let (_, wrongCheckpoint) ← mkTraceQuery mod (← `(traceSpec|
            $(mkIdent `advance):ident
            assert ($(mkIdent `count):ident = 4)
            any action))
          expectCheck "original trace" (← q.check w) .checked
          expectCheck "bad final edge" (← q.check { w with
            stateExprs := w.stateExprs.set! 2 w.stateExprs[0]! }) .invalid
          -- The twin has exactly the same effect, but the query requested advance.
          let twinPath := { w with labelExprs := w.labelExprs.set! 0 (mkConst ``Label.twin) }
          let (_, anyTwo) ← mkTraceQuery mod (← `(traceSpec| any 2 actions))
          expectCheck "legal twin edge" (← anyTwo.check twinPath) .checked
          expectCheck "wrong named action" (← q.check twinPath) .invalid
          expectCheck "intermediate assertion" (← wrongCheckpoint.check w) .invalid
          expectCheck "missing step" (← q.check { w with labelExprs := #[] }) .invalid
    | .induction md =>
      unless md.style == .tr && md.property == `zero && [`advance, `initializer].contains md.action do continue
      let original ← mod.mkInvariantGoalVC (mkIdent md.action) (mkIdent md.property) .tr
      liftTermElabM do
        let w ← buildCounterexampleExprs model.raw mod md.action
        let check := checkTRWitness mod original.toVCStatement md
        expectCheck "unmodified post" (← check w) .checked
        if md.action == `initializer then
          -- Induction starts the initializer from an arbitrary pre-state.
          expectCheck "initializer precondition" (← check { w with preStateExpr := w.postStateExpr.get! }) .checked
          return
        let four ← Term.elabTermAndSynthesize (← `(⟨4⟩)) (some w.stateType)
        expectCheck "wrong edge, violated clause" (← check { w with postStateExpr := some four }) .invalid
        expectCheck "legal edge, illegal pre" (← check { w with
          preStateExpr := w.postStateExpr.get!, postStateExpr := some four }) .invalid
        expectCheck "legal edge, preserved clause" (← check { w with
          postStateExpr := some w.preStateExpr
          labelExpr := some (← Term.elabTermAndSynthesize (← `(Label.advance 0)) none) }) .invalid
        expectCheck "false theory" (← check { w with
          theoryExpr := ← mkAppM ``Theory.mk #[mkConst ``Bool.false] }) .invalid
        expectCheck "disabled argument" (← check { w with
          labelExpr := some (← Term.elabTermAndSynthesize (← `(Label.advance 1)) none) }) .invalid
        expectCheck "unknown post" (← check { w with postStateExpr := none }) (.unverified "missing post-state")
    unless model.structuredJson.getObjValD "witnessCheck" == toJson WitnessCheck.checked do
      throwError "production replay for {vc.metadata}: {model.structuredJson.getObjValD "witnessCheck"}"
    numChecked := numChecked + 1
  unless numChecked == 5 do throwError "expected three traces and two TR failures, got {numChecked}"

-- Unused binders must still have genuine inhabitants.
private axiom bogus : Empty
run_cmd liftTermElabM do
  let template ← Term.elabType (← `(Empty → True))
  expectCheck "axiom in an unused argument" (← checkWitness <| specializeWitness template #[mkConst ``bogus]) (.unverified "nonstandard axiom in witness")
  expectCheck "replay resource limit" (← checkWitness (throwMaxRecDepthAt (← getRef))) (.unverified "replay resource limit reached")
end WitnessReplay
