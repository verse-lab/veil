module

public import Veil
set_option Elab.async false
public section

/- Candidate copied structurally from Lean 4.32 simpArrow's dependency-aware
   congruence branch. Prepared for validation, not yet compiled or tested.
   Include after importing Veil or Smt; this does not edit the dependency. -/

open Lean Meta Simp

namespace Issue123EmbeddingCandidate

meta def withAdditionalLemmas (xs : Array Expr) (f : SimpM α) : SimpM α := do
  Simp.withFreshCache do
    let mut s ← Simp.getSimpTheorems
    let mut updated := false
    let ctx ← Simp.getContext
    for x in xs do
      if ← isProof x then
        s ← s.addTheorem (.fvar x.fvarId!) x (config := ctx.indexConfig)
        updated := true
    if updated then Simp.withSimpTheorems s f else f

meta def contextualArrow (guard : Expr → Bool) : Simproc := fun e => do
  let .forallE n p q _ := e | return .continue
  -- This algorithm simplifies an originally nondependent implication.
  -- Let Lean's ordinary simpForall handle originally dependent proof binders.
  unless e.isArrow do return .continue
  unless guard p do return .continue
  let rp ← simp p
  let r ← Meta.withLocalDeclD n rp.expr fun hp => do
    let rq ← withAdditionalLemmas #[hp] (simp q)
    match rq.proof? with
    | none => mkImpCongr e rp rq
    | some hq =>
      let hq ← mkLambdaFVars #[hp] hq
      if rq.expr.containsFVar hp.fvarId! then
        return {
          expr := ← mkForallFVars #[hp] rq.expr
          proof? := ← withDefault <| mkImpDepCongrCtx (← rp.getProof) hq }
      else
        return {
          expr := e.updateForallE! rp.expr rq.expr
          proof? := ← withDefault <| mkImpCongrCtx (← rp.getProof) hq }
  return .done r

meta def fixedAddIntGtZeroLemma : Simproc :=
  contextualArrow Smt.Preprocess.Embedding.isIntGeLitZero

end Issue123EmbeddingCandidate


simproc ↓ [embedding] issue123_fixed_add_int_gt_zero (_ → _) :=
  Issue123EmbeddingCandidate.fixedAddIntGtZeroLemma
end

attribute [-embedding] Smt.Preprocess.Embedding.add_int_gt_zero
open Lean Elab Command in
run_cmd liftTermElabM do
  let some ext ← Meta.Simp.getSimprocExtension? `embedding | throwError "missing embedding extension"
  let procs ← ext.getSimprocs
  if procs.simprocNames.contains ``Smt.Preprocess.Embedding.add_int_gt_zero then
    throwError "original simproc unexpectedly active"
  unless procs.simprocNames.contains ``issue123_fixed_add_int_gt_zero do
    throwError "candidate simproc is not active"
  logInfo "ISSUE123: candidate active; original contextual Nat simproc disabled"


-- Original TLA+ file, Copyright: Igor Konnov
-- https://github.com/konnov/cyclic-buffer-challenge/blob/1e499eeb2923d70f5269aca877dc3180f3baccf9/tla/BuggyCircularBuffer.tla


public instance [NeZero N] : Inhabited { n : Nat // n ∈ List.range N } where
  default := ⟨0, by
    simp only [List.mem_range]
    have : N ≠ 0 := NeZero.ne N
    omega⟩

public instance (n : Nat) (N : Nat) [NeZero N] :  Inhabited (Std.TreeMap (Fin n) { t // t ∈ List.range N } compare) := by
  infer_instance

public instance :  Inhabited (Std.TreeMap (Fin 2) { n // n ∈ List.range 2 } compare) := by
  infer_instance

veil module BuggyCircularBuffer

abbrev BUFFER_ELEMS := (List.range 2 : List Nat)
abbrev ExtTreeElem := { n : Nat // n ∈ BUFFER_ELEMS }
abbrev BUFFER_SIZE := 2

function buffer : Fin BUFFER_SIZE → ExtTreeElem
individual head : Nat
individual tail : Fin BUFFER_SIZE
individual count : Nat

#gen_state

after_init {
  buffer := fun _ => ⟨0, by simp⟩
  head := (0 : Nat)
  tail := (0 : Fin BUFFER_SIZE)
  count := (0 : Nat)
}

/- There is not any high-bound guard condition
for this action, so it can be executed infinite times.-/
action Put {
  let x ← pick ExtTreeElem
  buffer tail := x
  head := head
  tail := Fin.mk ((tail.val + 1) % BUFFER_SIZE) (by grind)
  count := count + 1
}

action Get {
  require count > 0
  head := (head + 1) % BUFFER_SIZE
  tail := tail
  count := count - 1
}

safety count ≤ BUFFER_SIZE


#gen_spec
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
unsat trace [production_probe] {
  any action
  assert (count > BUFFER_SIZE)
} by
  veil_bmc
end BuggyCircularBuffer
