import Lean

namespace Veil

/-- Attribute added to `Wp` constructs, to unfold them. -/
register_simp_attr wpSimp

/-- Attribute added to `wp` equations of monadic constructs and actions/procedures. -/
register_simp_attr wpEqSimp

/-- Attribute added to `.wpgen` definitions of actions/procedures. -/
register_simp_attr wpDefUnfoldSimp

/-- Attribute added to definitions/theorems related to `IsSubStateOf` and `IsSubReaderOf`. -/
register_simp_attr substateSimp

/-- Attribute added to `StateAssertion`s, to unfold them. Despite what
the might suggest, this is also added to `safety`, `trusted invariant`,
and `assumption` assertions. -/
register_simp_attr invSimp

/-- Attribute added to `DerivedDefinition`s that are `.invariantLike`
or `.assumptionLike`, to unfold them. -/
register_simp_attr derivedInvSimp

/-- Attribute added to Veil actions, to unfold them. -/
register_simp_attr actSimp

/-- Attribute added to `DerivedDefinition`s that are `.actionLike`, to unfold them. -/
register_simp_attr derivedActSimp

/-- Attribute added to theorems about invariants. -/
register_simp_attr invProof

/-- Lemmas to perform simplification of `if` expressions, before `split_ifs` is
called. -/
register_simp_attr ifSimp

register_simp_attr fieldRepresentationPatSimp
register_simp_attr fieldRepresentationSetSimpPre
register_simp_attr fieldRepresentationSetSimpPost

/-- To enable `assumption`s to be used as predicates. -/
instance funOneArgBoolToProp : Coe (α → Bool) (α → Prop) where
  coe f a := f a = true

/-- To enable `invariant`s to be used as predicates. -/
instance funTwoArgsBoolToProp : Coe (α → β → Bool) (α → β → Prop) where
  coe f a b := f a b = true

/-- Used to hoist higher-order quantification to the top of the goal. -/
register_simp_attr quantifierSimp

namespace Simp
open Lean Elab

/-- `simps` can be either the names of simp sets (simp attributes) or the names
of theorems and/or definitions in the global environment. -/
def mkVeilSimpCtx (simps : Array Name) (config : Meta.Simp.Config := {}): MetaM Meta.Simp.Context := do
  let simpOnlyTheorems ← Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) ({} : Meta.SimpTheorems)
  let constSimps ← getSimpTheoremsFromConsts simps
  let simpsets ← getSimpTheoremsFromSimpSets simps
  let congrTheorems ← Meta.getSimpCongrTheorems
  Meta.Simp.mkContext config (simpTheorems := #[simpOnlyTheorems, constSimps] ++ simpsets) (congrTheorems := congrTheorems)
where
  getSimpTheoremsFromSimpSets (simps : Array Name) : CoreM (Array Meta.SimpTheorems) := do
    let simpExts ← simps.filterMapM (Meta.getSimpExtension? ·)
    simpExts.mapM (·.getTheorems)
  getSimpTheoremsFromConsts (simps : Array Name) : MetaM (Meta.SimpTheorems) := do
    -- based on `Lean.Elab.Tactic.elabDeclToUnfoldOrTheorem`
    let simps : Array (Array Meta.SimpTheorem ⊕ Array Meta.SimpEntry) ← simps.filterMapM (fun name => do
      let [(fqn, _)] ← resolveGlobalName name | return none
      let info ← getConstVal fqn
      if (← Meta.isProp info.type) then
        -- TODO: `post := false` means `↓`, `inv := true` means `←`
        let thms ← Meta.mkSimpTheoremFromConst fqn (post := true) (inv := false)
        return some (.inl thms)
      else
        let simpEntries ← Meta.mkSimpEntryOfDeclToUnfold fqn
        return (some (.inr simpEntries)))
    let simpTheorems  := simps.filterMap (fun s =>  match s with | .inl thms => some thms | .inr _ => none) |>.flatten
    let simpEntries := simps.filterMap (fun s =>  match s with | .inr entries => some entries | .inl _ => none) |>.flatten
    let s := simpTheorems.foldl (init := default) (fun thms thm => thms.addSimpTheorem thm)
    let s := simpEntries.foldl (init := s) (fun thms entry => thms.addSimpEntry entry)
    return s

def EqualityProof := Option Expr
/-- This not exactly a `Simproc`, since we don't return intermediate `Step`s. -/
def Simplifier := Expr → MetaM Meta.Simp.Result

/-- A simplifier that does nothing. -/
def Simplifier.id : Simplifier := fun e => return { expr := e }

/-- Sequentially compose two simplifiers. -/
def Simplifier.andThen (s1 : Simplifier) (s2 : Simplifier) : Simplifier := fun e => do
  let res1 ← s1 e
  let res2 ← s2 res1.expr
  res1.mkEqTrans res2

def unfold (defs : Array Name) : Simplifier := fun e => do
  let mut res : Meta.Simp.Result := { expr := e }
  for name in defs do
    let res' ← Meta.unfold res.expr name
    res ← res.mkEqTrans res'
  trace[veil.debug] "unfold {defs}\n{e}\n~>\n{res.expr}"
  return res

def simpCore (ctx : Meta.Simp.Context) (simps : Array Name := #[]) : Simplifier := fun e => do
  let (res, _stats) ← Meta.simp e ctx (discharge? := none)
  let _usedTheorems := _stats.usedTheorems.toArray.map (·.key)
  trace[veil.debug] "simp {simps} (used: {_usedTheorems}):\n{e}\n~>\n{res.expr}"
  return res

def simp (simps : Array Name) (config : Meta.Simp.Config := {}) : Simplifier := fun e => do
  simpCore (← mkVeilSimpCtx simps config) simps e

def dsimp (simps : Array Name) (config : Meta.Simp.Config := {}) : Simplifier := fun e => do
  let (expr, _stats) ← Meta.dsimp e (← mkVeilSimpCtx simps config)
  let _usedTheorems := _stats.usedTheorems.toArray.map (·.key)
  trace[veil.debug] "dsimp {simps} (used: {_usedTheorems}):\n{e}\n~>\n{expr}"
  return { expr := expr }

open Meta Elab Term in
def elabInlineDSimp (idts : TSyntaxArray `ident) (t : TSyntax `term) (expectedType? : Option Expr) : TermElabM Simp.Result := do
  let things := idts.map Syntax.getId
  let t ← withSynthesize (postpone := .partial) do
    elabTerm t expectedType?
  synthesizeSyntheticMVars
  let t ← instantiateMVars t
  let res ← dsimp things {} t
  return res

syntax (name := inlineDSimpStx) "dsimp% " "[" ident,* "] " term : term

open Meta Elab Term in
@[term_elab inlineDSimpStx]
def elabDecidableReplace : TermElab := fun stx expectedType? =>
  match stx with
  | `(dsimp% [ $[$idts:ident],* ] $t) => do
    let res ← elabInlineDSimp idts t expectedType?
    pure res.expr
  | _ => throwUnsupportedSyntax

end Simp

end Veil
