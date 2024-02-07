-- FIXME: I'm not sure why this is needed
import Mathlib.Tactic
import Lean

def updateFn [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  λ (x : α) => if x = a then b else f x

notation st"[ " a " ↦ " b " ]" => updateFn st a b

@[simp] lemma updateFn_unfold [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
  (f[a ↦ b]) x = if x = a then b else f x := by
  simp only [updateFn]

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
