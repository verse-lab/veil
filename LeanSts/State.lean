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

structure FOStructure (σ₁) :=
  ex_individual : σ₁
  -- ex_relation : σ₁ → σ₁ → Prop
  -- ex_function : σ₁ → σ₂

open SlimCheck
instance FOStructure.SampleableExt (σ₁ : Type u) [SampleableExt σ₁] :
  SampleableExt (FOStructure σ₁)
  where
  proxy : Type u := SampleableExt.proxy σ₁
  interp := fun a => ⟨SampleableExt.interp a⟩
  sample := @SampleableExt.sample σ₁ _

-- set_option pp.all false
#sample (FOStructure Bool)
-- #sample String

open SampleableExt
-- set_option trace.Meta.synthInstance true

structure FOStructure' (σ₁ σ₂) :=
  ex_individual : σ₁
  ex_function : σ₂ → Bool

#check TotalFunction.Pi.sampleableExt
-- set_option synthInstance.maxHeartbeats 80000

section
variable [SampleableExt σ₁] [Repr σ₁] [DecidableEq σ₁] [SampleableExt σ₂]
#check SampleableExt.proxy (σ₁ → σ₂)
end

#sample (Nat × Nat → Bool)

instance FOStructure'.SampleableExt (σ₁ : Type u) (σ₂ : Type v)
  [SampleableExt.{_, u} σ₁] [Repr σ₁] [DecidableEq σ₁]
  [SampleableExt.{_, v} σ₂] [Repr σ₂] [DecidableEq σ₂]
  :
  SampleableExt (FOStructure' σ₁ σ₂)
  where
  proxy := Prod (SampleableExt.proxy σ₁) (SampleableExt.proxy (σ₂ → Bool))
  interp := fun ⟨a, b⟩ => ⟨SampleableExt.interp a, SampleableExt.interp b⟩
  sample := Gen.prodOf sample sample

-- TODO:
-- add a generator fo FOStructure based on `sort`, `individual`, `relation`,
-- and `function` declarations, like in Ivy/mypyvy.

-- syntax (name := declareSort) "sort" : command
-- @[command_elab declareSort]
-- def declareSortImpl : CommandElab := fun stx => do
--   logInfo s!"declaring sort {stx}"

-- open Lean in
-- elab "sort" sorts:ident* : command =>
--   if sorts.size == 0 then
--     throwError "at least one sort must be provided"
--   else if sorts.size == 1 then
--     let sort := sorts[0]! -- `sorts` is not empty
--     logInfo s!"declaring sort {sort}"
--   else
--     let sorts := sorts.map fun sort => toString sort
--     logInfo s!"declaring sorts {sorts}"

-- open Lean Elab in
-- elab "xxx" sorts:ident* : command => do
--   let env ← getEnv
--   for s in sorts do
--     let name ← resolveGlobalConstNoOverload s
--     logInfo s!"xxx {name}"

-- xxx Nat

-- open Lean Parser Command in
-- macro "declare_state" name:ident xs:ident* : command => do
--   let fields ← xs.mapM fun x => `(structExplicitBinder| ($x:ident : Nat))
--   let fieldsStx : TSyntax ``structFields ← `(structFields| $fields*)
--   `(structure $name where
--       $fieldsStx:structFields)

-- declare_state R2 x y
-- declare_state R3 x y z

-- #print R3
