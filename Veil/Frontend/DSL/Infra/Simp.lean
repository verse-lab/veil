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

/-- Implementation detail. Tagged to `act.do` and constructs that
should be unfolded when elaborating action's definitions. -/
register_simp_attr doSimp

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
  let simpsets ← getSimpTheoremsFromSimpSets simps
  let simps ← getSimpTheoremsFromConsts simps
  let congrTheorems ← Meta.getSimpCongrTheorems
  Meta.Simp.mkContext config (simpTheorems := simpsets ++ #[simps]) (congrTheorems := congrTheorems)
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

def simp (simps : Array Name) (config : Meta.Simp.Config := {}) : Simplifier := fun e => do
  let (res, _stats) ← Meta.simp e (← mkVeilSimpCtx simps config) (discharge? := none)
  trace[veil.debug] "simp {simps}\n{e}\n~>\n{res.expr}"
  return res

def dsimp (simps : Array Name) (config : Meta.Simp.Config := {}) : Simplifier := fun e => do
  let (expr, _stats) ← Meta.dsimp e (← mkVeilSimpCtx simps config)
  trace[veil.debug] "dsimp {simps}\n{e}\n~>\n{expr}"
  return { expr := expr }

end Simp

end Veil
