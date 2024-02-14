-- FIXME: I'm not sure why this is needed
import Mathlib.Tactic
import LeanSts.Testing
-- import Lean

def updateFn [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  λ (x : α) => if x = a then b else f x

def updateFn2 [DecidableEq α] [DecidableEq β] (f : α → β → γ)  (a : α) (b : β) (c : γ) : α → β → γ :=
  λ (x : α) (y : β) => if x = a && y = b then c else f x y

notation f"[ " a " ↦ " b " ]" => updateFn f a b
notation f"[ " a " , " b " ↦ " c " ]" => updateFn2 f a b c

@[simp] lemma updateFn_unfold [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
  (f[a ↦ b]) x = if x = a then b else f x := by
  simp only [updateFn]

@[simp] lemma updateFn2_unfold  [DecidableEq α] [DecidableEq β] (f : α → β → γ)  (a : α) (b : β) (c : γ) :
  (f[a , b ↦ c]) x y = if x = a && y = b then c else f x y := by
  simp only [updateFn2]

-- TODO: write a macro to define SampleableExt instances for Structures
-- See https://github.com/verse-lab/lean-sts/commit/228605e7bb54c9f7cfec5d437f79c9607fb413fa
-- for an example.

open Lean in
initialize
  registerTraceClass `gen_smt
