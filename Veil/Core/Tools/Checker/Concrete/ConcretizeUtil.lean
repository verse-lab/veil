import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.State.Types
import Mathlib.Data.FinEnum
import Veil.Util.Meta

import Veil.Core.Tools.Checker.Concrete.modelCheckerView
import ProofWidgets.Component.HtmlDisplay

import Lean.Parser.Term
open Lean Elab Command Veil
open Lean Elab Command

/-- Collect all Veil variable binders from a module. -/
def Module.collectVeilVarsBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module)
  : m (Std.HashMap Name (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  mod.parameters.foldlM (init := {}) fun acc p => do
    let b ← p.binder
    pure <| acc.insert p.name b

structure BinderConfig where
  suffix : Option String := none

  instName : Option Name := none
  /-- Error message prefix if binder not found -/
  errPrefix : String := "No binder found"

/-- Collect binders from a module based on configuration. -/
def collectBinders [Monad m] [MonadQuotation m] [MonadError m]
    (mod : Veil.Module)
    (config : BinderConfig)
    : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  match config.instName with
  | some instName =>
    -- Collect instance binders (e.g., Ord, FinEnum)
    let instNamePostfix := instNameToPostfix instName
    let ids : Array Ident ← mod.sortIdents
    ids.mapM (fun t : Ident => do
      let name' := t.getId.appendAfter instNamePostfix
      `(bracketedBinder| [$(mkIdent name') : $(mkIdent instName) $t]))
  | none =>
    -- Collect explicit type binders with optional suffix
    let typeIdents : Array (TSyntax `ident) ← mod.sortIdents
    let varsBinders ← Module.collectVeilVarsBinders mod
    typeIdents.mapM fun t : (TSyntax `ident) => do
      let base := t.getId
      let key := match config.suffix with
                 | none => base
                 | some suf => base.appendAfter suf
      match varsBinders[key]? with
      | some b => pure b
      | none => throwError m!"{config.errPrefix} for type {t}"
where
  instNameToPostfix (instName : Name) : String :=
    match instName with
    | ``Ord       => "_ord"
    | ``FinEnum   => "_fin_enum"
    | ``Hashable  => "_hash"
    | ``ToJson    => "_to_json"
    | ``Repr      => "_repr"
    | ``Veil.Enumeration => "_enumeration"
    | _           => "_anonymous_inst"

/-- Given name of instance like `Ord`, return all the instance binders for all the types. -/
def Veil.Module.instBinders [Monad m] [MonadQuotation m] [MonadError m] (mod : Veil.Module) (instName : Name)
  : m (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  collectBinders mod { instName := some instName }

/-- Generate propCmp (e.g., `TransCmp`, `LawfulEqCmp`) binder for a given type. -/
def propCmpBinder [Monad m] [MonadQuotation m] [MonadError m]
    (propName : Name)
    (sortIdent : Ident)
    : m (TSyntax `Lean.Parser.Term.bracketedBinder) := do
  let instNamePostfix := propNameToPostfix propName
  let name' := sortIdent.getId.appendAfter instNamePostfix
  `(bracketedBinder| [$(mkIdent name') : $(mkIdent propName) ($(mkIdent ``Ord.compare) ($(mkIdent `self) := $(mkIdent ``inferInstanceAs) ($(mkIdent ``Ord) $sortIdent)))])
where
  propNameToPostfix (propName : Name) : String :=
    match propName with
    | ``Std.TransCmp    => "_trans_cmp"
    | ``Std.LawfulEqCmp => "_lawful_cmp"
    | ``Std.OrientedCmp => "_oriented_cmp"
    | _                 => "_anonymous_prop_cmp"

/-- Collect comprehensive binders for NextAct and executable list generation.
    Includes: FinEnum, Hashable, Ord, LawfulEqCmp, and TransCmp instances. -/
def Veil.Module.collectNextActBinders (mod : Veil.Module) : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let sortIdents ← mod.sortIdents
  -- let finEnumInsts ← mod.instBinders ``FinEnum
  let finEnumInsts ← mod.instBinders ``Veil.Enumeration
  let hashInsts ← mod.instBinders ``Hashable
  let ordInsts ← mod.instBinders ``Ord
  let lawfulInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.LawfulEqCmp id)
  let transInsts ← sortIdents.mapM (fun id => propCmpBinder ``Std.TransCmp id)
  return finEnumInsts ++ hashInsts ++ ordInsts ++ lawfulInsts ++ transInsts
