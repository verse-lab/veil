import Veil.Util.Meta

namespace Veil

/-- Attribute added to `Wp` constructs, to unfold them. -/
register_simp_attr wpSimp

/-- Attribute added to `.wpgen` definitions of actions/procedures. -/
register_simp_attr wpDefUnfoldSimp

/-- Attribute added to proof-producing ITE compactification rules for generated
WP predicates.  These rules preserve `letEq` sharing barriers and should only
be used in the WP compactification pipeline, not in general SMT preprocessing. -/
register_simp_attr wpCompactIteSimp

/-- Attribute added to generated abstract-state eta rules used after
`wpCompactIteSimp` has pushed branch conditions into post-state arguments. -/
register_simp_attr wpCompactStateSimp

/-- Attribute added to definitions/theorems related to `IsSubStateOf` and `IsSubReaderOf`. -/
register_simp_attr substateSimp

/-- Attribute added to `StateAssertion`s, to unfold them. Despite what
the might suggest, this is also added to `safety`, `trusted invariant`,
and `assumption` assertions. -/
register_simp_attr invSimp

/-- Attribute added to `DerivedDefinition`s that are `.invariantLike`
or `.assumptionLike`, to unfold them. -/
register_simp_attr derivedInvSimp

/-- Attribute added to `DerivedDefinition`s that are `.ghost`,
to unfold them. -/
register_simp_attr ghostRelSimp

/-- Attribute added to Veil actions, to unfold them. -/
register_simp_attr actSimp

/-- Attribute added for simplifications done for symbolic model checking. -/
register_simp_attr nextSimp

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

register_simp_attr dsimpFieldRepresentationGet
register_simp_attr dsimpFieldRepresentationSet

/-- Attribute added to the results of multi-extraction of type `ConstrainedExtractResult`
and some other things. Used for simplify the results of multi-extraction
in the form of monadic programs. -/
register_simp_attr multiExtractSimp

register_simp_attr loomLogicSimpForVeil

/-- To enable `assumption`s to be used as predicates. -/
instance funOneArgBoolToProp : Coe (α → Bool) (α → Prop) where
  coe f a := f a = true

/-- To enable `invariant`s to be used as predicates. -/
instance funTwoArgsBoolToProp : Coe (α → β → Bool) (α → β → Prop) where
  coe f a b := f a b = true

/-- Used to hoist higher-order quantification to the top of the goal. -/
register_simp_attr forallQuantifierSimp
register_simp_attr existsQuantifierSimp

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

def unfold (defs : Array Name) : Simplifier := fun e => withBackwardsCompatibility do
  let mut res : Meta.Simp.Result := { expr := e }
  for name in defs do
    let res' ← Meta.unfold res.expr name
    res ← res.mkEqTrans res'
  trace[veil.debug] "unfold {defs}\n{e}\n~>\n{res.expr}"
  return res

private def getSimprocs (simps : Array Name) : CoreM Meta.Simp.SimprocsArray := do
  let mut simprocs : Meta.Simp.SimprocsArray := #[{ : Meta.Simp.Simprocs }]
  for a in simps do
    if (← Meta.Simp.isSimproc a) then
      simprocs ← simprocs.add a false     -- maybe change this later
    else if let some ext ← Meta.Simp.getSimprocExtension? a then
      simprocs := simprocs.push (← ext.getSimprocs)
  return simprocs

/-- Prove a definitional equality without asking the kernel to compare a
large reducible head.  In particular, for a junction `wp a p = wp b p`, push
the definitional comparison down to `a = b` and lift it back with `congrArg`.
The remaining reflexivity proof then unfolds only the small differing
subterm (for example `returnUnit`), rather than symbolically evaluating
`wp`. -/
private partial def mkIsolatedDefEqProof (a b : Expr) : MetaM Expr := do
  if a == b then
    return ← Meta.mkEqRefl a
  if let some proof ← etaProof? a b then
    return proof
  -- `observing?` rolls back the attempt's metavariables when congruence does
  -- not apply.
  if let some proof ← observing? (congrProof a.consumeMData b.consumeMData) then
    return proof
  -- The surrounding application structure has been peeled away as far as
  -- possible.  Keep the final definitional check local to this subterm.  If
  -- the endpoints are not actually definitionally equal, the kernel will
  -- reject this expected-type hint when it checks the generated theorem.
  Meta.mkExpectedTypeHint (← Meta.mkEqRefl a) (← Meta.mkEq a b)
where
  /-- Build an explicit `funext` proof when `a` and `b` differ only by head
  eta-expansion.  Such a proof keeps the kernel from choosing expensive delta
  reduction at equality-proof junctions. -/
  etaProof? (a b : Expr) : MetaM (Option Expr) := do
    if a == b then
      return some (← Meta.mkEqRefl a)
    match a, b with
    | .lam n t body bi, _ =>
      Meta.withLocalDecl n bi t fun x => do
        /- Recurse on the head-beta form: when `b` is itself a lambda (an eta
        gap under a binder), `mkApp b x` never becomes syntactically equal to
        the instantiated body without it. The inner proof's endpoints then
        differ from `mkApp b x` only by beta, which the kernel closes cheaply
        (whnf-core), unlike delta. -/
        let bx := mkApp b x
        let some inner ← etaProof? (body.instantiate1 x) bx.headBeta | return none
        /- Build `funext` explicitly rather than via `Meta.mkFunExt`: the
        endpoints must be exactly `a` and `b` (not their eta-expansions), or
        the kernel closes the gap by reducing the whole body and times out. -/
        let bxTy ← Meta.inferType bx
        let β ← Meta.mkLambdaFVars #[x] bxTy
        let h ← Meta.mkLambdaFVars #[x] inner
        let u ← Meta.getLevel t
        let v ← Meta.getLevel bxTy
        return some <| mkAppN (mkConst ``funext [u, v]) #[t, β, a, b, h]
    | _, .lam .. => (← etaProof? b a).mapM Meta.mkEqSymm
    | _, _ => return none
  /-- Does this application change an argument on which the type of a later
  argument depends?  Such a change cannot be lifted with ordinary `congrArg`,
  and constructing the motive would not notice: `inferType` assumes
  well-typedness, so the ill-typed proof would only fail in the kernel. -/
  changesDependentArgument (fn : Expr) (aArgs bArgs : Array Expr) : MetaM Bool := do
    Meta.forallBoundedTelescope (← Meta.inferType fn) (some aArgs.size) fun xs _ => do
      for i in [:min xs.size aArgs.size] do
        unless aArgs[i]!.consumeMData == bArgs[i]!.consumeMData do
          for x in xs[i+1:] do
            if (← Meta.inferType x).containsFVar xs[i]!.fvarId! then
              return true
      return false
  /-- Rewrite the differing arguments under a shared application head one at
  a time, lifting each argument's recursively isolated proof with `congrArg`.
  Throws if the endpoints do not share an application head, if no argument
  differs, or if `congrArg` is inapplicable. -/
  congrProof (a b : Expr) : MetaM Expr := do
    let fn := a.getAppFn.consumeMData
    let aArgs := a.getAppArgs
    let bArgs := b.getAppArgs
    unless fn == b.getAppFn.consumeMData && aArgs.size == bArgs.size do
      throwError "the endpoints do not share an application head"
    if ← changesDependentArgument fn aArgs bArgs then
      throwError "a changed argument has later dependent arguments"
    let mut args := aArgs
    let mut proof? : Option Expr := none
    for i in [:args.size] do
      let src := args[i]!
      let tgt := bArgs[i]!
      unless src.consumeMData == tgt.consumeMData do
        let argProof ← mkIsolatedDefEqProof src tgt
        let cur := args
        let congrFn ← Meta.withLocalDeclD `_junction (← Meta.inferType src) fun x =>
          Meta.mkLambdaFVars #[x] (mkAppN fn (cur.set! i x))
        let step ← Meta.mkCongrArg congrFn argProof
        proof? := some (← proof?.elim (pure step) (Meta.mkEqTrans · step))
        args := args.set! i tgt
    let some proof := proof? | throwError "no application argument changed"
    return proof

/-- Insert explicit eta/congruence bridges between the pieces of a
simp-generated `Eq.trans` proof, recursing into congruence-lemma arguments
(`congrArg`, `funext`, `ite_congr`, …).

An unbridged junction forces the kernel to close the gap definitionally, and
for an eta gap over an interpreter application (`wp prog post` vs
`fun r s => wp prog post r s`) the kernel delta-normalizes the application
side before its eta rule applies — a deterministic timeout in practice (see
`kernel_defeq_eta_repro.lean`). Simp nests such junctions inside congruence
arguments (e.g. `ite_congr`'s branch proofs, under `funext` binders), so
healing only the top-level spine is not enough. Rewriting proof-positioned
subterms is type-safe: healing preserves a chain's endpoints, and embedded
proofs are irrelevant to the kernel. -/
partial def healEqTransJunctions (proof : Expr) : MetaM Expr := do
  let e := proof.consumeMData
  if e.isLambda then
    Meta.lambdaTelescope e fun xs body => do
      let body' ← healEqTransJunctions body
      if body' == body then return proof else Meta.mkLambdaFVars xs body'
  else if e.getAppFn.isConstOf ``Eq.trans && e.getAppNumArgs == 6 then
    healChain e
  else if e.isApp then
    let args := e.getAppArgs
    let args' ← args.mapM healArg
    if args' == args then return proof else return mkAppN e.getAppFn args'
  else
    return proof
where
  /-- Recurse into proof arguments (their statements are untouched, so the
  surrounding application stays well-typed) and into lambdas, whose bodies
  may be proofs under binders (`funext`/`ite_congr` arguments); a proof
  embedded in a non-proof lambda is irrelevant to the kernel, so rewriting it
  is harmless. -/
  healArg (a : Expr) : MetaM Expr := do
    let a' := a.consumeMData
    if a'.isLambda then
      healEqTransJunctions a
    else if a'.isApp && (← try Meta.isProp (← Meta.inferType a') catch _ => pure false) then
      healEqTransJunctions a
    else
      return a
  /-- Heal one `Eq.trans` chain: heal the legs recursively, then re-chain
  them, bridging junctions whose adjacent endpoints differ syntactically. -/
  healChain (e : Expr) : MetaM Expr := do
    -- accumulated proof and its right endpoint
    let mut acc? : Option (Expr × Expr) := none
    for part in ← (spine e).mapM healEqTransJunctions do
      let some (_, lhs, rhs) := (← Meta.inferType part).eq? | return e
      match acc? with
      | none => acc? := some (part, rhs)
      | some (accProof, accRhs) =>
        let bridged ← if accRhs == lhs then pure accProof else
          Meta.mkEqTrans accProof (← mkIsolatedDefEqProof accRhs lhs)
        acc? := some (← Meta.mkEqTrans bridged part, rhs)
    return ((acc?.map (·.1)).getD e)
  /-- The leaf proofs of a nested `Eq.trans` chain, left to right. -/
  spine (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
    let e := e.consumeMData
    let args := e.getAppArgs
    if e.getAppFn.isConstOf ``Eq.trans && args.size == 6 then
      spine args[5]! (spine args[4]! acc)
    else
      acc.push e

def simpCore (ctx : Meta.Simp.Context) (simps : Array Name := #[]) : Simplifier := fun e => withBackwardsCompatibility do
  let (res, _stats) ← Meta.simp e ctx (discharge? := none) (simprocs := ← getSimprocs simps)
  let _usedTheorems := _stats.usedTheorems.toArray.map (·.key)
  trace[veil.debug] "simp {simps} (used: {_usedTheorems}):\n{e}\n~>\n{res.expr}"
  return res

def simp (simps : Array Name) (config : Meta.Simp.Config := {}) : Simplifier := fun e => withBackwardsCompatibility do
  simpCore (← mkVeilSimpCtx simps config) simps e

def dsimp (simps : Array Name) (config : Meta.Simp.Config := {}) : Simplifier := fun e => withBackwardsCompatibility do
  let (expr, _stats) ← Meta.dsimp e (← mkVeilSimpCtx simps config) (simprocs := ← getSimprocs simps)
  let _usedTheorems := _stats.usedTheorems.toArray.map (·.key)
  trace[veil.debug] "dsimp {simps} (used: {_usedTheorems}):\n{e}\n~>\n{expr}"
  return { expr := expr }

open Meta Elab Term Parser.Tactic

private def elabTermBeforeDSimpOrUnfold (t : TSyntax `term) (expectedType? : Option Expr) : TermElabM Expr := do
  let t ← withSynthesize (postpone := .partial) do
    elabTerm t expectedType?
  synthesizeSyntheticMVars
  instantiateMVars t

private def interpretConfigItems (c : TSyntaxArray ``configItem) : Option Meta.Simp.Config := do
  let mut res := { : Meta.Simp.Config }
  for item in c do
    match item with
    | `(configItem| +$option) => res ← interpretConfigItemWithSign res true option.getId
    | `(configItem| -$option) => res ← interpretConfigItemWithSign res false option.getId
    | _ => failure
  return res
where interpretConfigItemWithSign (a : Meta.Simp.Config) (sign : Bool) (field : Name) : Option Meta.Simp.Config :=
  match field with
  | `zeta => some { a with zeta := sign }
  | `eta => some { a with eta := sign }
  | `proj => some { a with proj := sign }
  | `iota => some { a with iota := sign }
  | `beta => some { a with beta := sign }
  | `failIfUnchanged => some { a with failIfUnchanged := sign }
  | `unfoldPartialApp => some { a with unfoldPartialApp := sign }
  | `instances => some { a with instances := sign }
  | _ => none

-- NOTE: We could use `Lean.Parser.Tactic.optConfig` for `cfg`, but
-- `elabDSimpConfigCore` and similar derived elaborators are for
-- `TacticM`, so here we use a simpler approach: only recognizing
-- some basic options.
def elabInlineDSimp (idts : TSyntaxArray `ident) (cfgitems : TSyntaxArray ``configItem) (t : TSyntax `term) (expectedType? : Option Expr) : TermElabM Simp.Result := do
  let t ← elabTermBeforeDSimpOrUnfold t expectedType?
  let things := idts.map Syntax.getId
  let some cfg := interpretConfigItems cfgitems
    | throwError "failed to interpret dsimp config items: {cfgitems}"
  let res ← dsimp things cfg t
  return res

def elabInlineUnfold (idts : TSyntaxArray `ident) (t : TSyntax `term) (expectedType? : Option Expr) : TermElabM Simp.Result := do
  let t ← elabTermBeforeDSimpOrUnfold t expectedType?
  let things := idts.map Syntax.getId
  let res ← unfold things t
  return res

syntax (name := inlineDSimpStx) "veil_dsimp% " configItem* "[" ident,* "] " term : term
syntax (name := inlineUnfoldStx) "veil_unfold% " "[" ident,* "] " term : term

@[term_elab inlineDSimpStx]
def elabInlineDSimpStx : TermElab := fun stx expectedType? =>
  match stx with
  | `(veil_dsimp% $cfgitems:configItem* [ $[$idts:ident],* ] $t) => do
    let res ← elabInlineDSimp idts cfgitems t expectedType?
    pure res.expr
  | _ => throwUnsupportedSyntax

@[term_elab inlineUnfoldStx]
def elabInlineUnfoldStx : TermElab := fun stx expectedType? =>
  match stx with
  | `(veil_unfold% [ $[$idts:ident],* ] $t) => do
    let res ← elabInlineUnfold idts t expectedType?
    pure res.expr
  | _ => throwUnsupportedSyntax

end Simp

end Veil
