-- FIXME: I'm not sure why this is needed
import Mathlib.Tactic
import LeanSts.Testing
-- import Lean

def updateFn [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  λ (x : α) => if x = a then b else f x

notation st"[ " a " ↦ " b " ]" => updateFn st a b

@[simp] lemma updateFn_unfold [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
  (f[a ↦ b]) x = if x = a then b else f x := by
  simp only [updateFn]

-- TODO: write a macro to define SampleableExt instances for Structures
-- See https://github.com/verse-lab/lean-sts/commit/228605e7bb54c9f7cfec5d437f79c9607fb413fa
-- for an example.
