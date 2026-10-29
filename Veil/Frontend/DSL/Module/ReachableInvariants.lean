module

public meta import Veil.Frontend.DSL.Module.Util
public meta import Veil.Frontend.DSL.Module.VCGen
public import Veil.Frontend.DSL.Action.Semantics.Theorems
public import Veil.Frontend.DSL.Action.Semantics.NativeTransition
public meta import Lean.Util.CollectAxioms

public meta section

open Lean Elab Command

namespace Veil

/-- Sort replacements used only in the exported reachability theorem. -/
abbrev ReachableInvariantSubst := Std.HashMap Name Term

private def mentionsSubstitution (substs : ReachableInvariantSubst) (stx : Syntax) : Bool :=
  (stx.find? fun t => t.isIdent && substs.contains t.getId).isSome

private partial def substituteSyntax (substs : ReachableInvariantSubst) (stx : Syntax) : Syntax :=
  if stx.isIdent then
    (substs[stx.getId]?).map (·.raw) |>.getD stx
  else stx.setArgs (stx.getArgs.map (substituteSyntax substs))

private def argSubst (substs : ReachableInvariantSubst) (p : Parameter) : CommandElabM Term := do
  if let some t := substs[p.name]? then return t
  match p.kind with
  | .moduleTypeclass .userDefined => p.arg
  | .moduleTypeclass _ | .definitionParameter _ .typeclass =>
      if mentionsSubstitution substs p.type then `(term| inferInstance) else p.arg
  | _ => p.arg

private def binderSubst? (substs : ReachableInvariantSubst) (p : Parameter) :
    CommandElabM (Option (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  if substs.contains p.name then return none
  match p.kind with
  | .moduleTypeclass .sortAssumption =>
      if mentionsSubstitution substs p.type then return none
  | _ => pure ()
  return some (← ({ p with «type» := ⟨substituteSyntax substs p.type⟩ } : Parameter).binder)

private def preservationTheoremName (act inv : Name) (tr : Bool) : Name :=
  Name.mkSimple s!"{act}_{inv}{if tr then "_tr" else ""}"

private def generatedInvariantsTheoremName : Name :=
  assembledInvariantsName ++ `is_inv

/-! ## Substitution Parsing & Validation -/

private def parseReachableInvariantSubstitutions
    (substs : Array (TSyntax `theoremSortSubstitution)) :
    CommandElabM ReachableInvariantSubst := do
  let mut result : ReachableInvariantSubst := {}
  for stx in substs do
    match stx with
    | `(theoremSortSubstitution| $id:ident := $term:term) =>
        let name := id.getId
        if result.contains name then
          throwErrorAt stx "duplicate substitution for module sort {name}"
        result := result.insert name term
    | _ => throwUnsupportedSyntax
  return result

private def validateReachableInvariantSubstitutions
    (mod : Module) (substs : ReachableInvariantSubst) : CommandElabM Unit := do
  let sortNames := Std.HashSet.ofArray (mod.parameters.filterMap fun p => match p.kind with | .sort _ => some p.name | _ => none)
  for (name, _) in substs do
    unless sortNames.contains name do
      throwError "#gen_theorems only supports substitutions for module sorts; \
        `{name}` is not a sort parameter of module {mod.name}"

/-! ## TR-Theorem Availability Check -/

private def theoremAvailable (name : Name) : CommandElabM Bool := do
  let some info := (← getEnv).find? ((← getCurrNamespace) ++ name)
    | return false
  let mgr ← Verifier.vcManager.atomically fun ref => ref.get
  for id in mgr.vcIdsInDependencyOrder do
    if let some (vc, _) := mgr.provenWitness? id then
      if vc.name == name then
        -- Exact type plus an actual completed discharger: an unrelated
        -- right-typed stub cannot cover an unchecked or failed obligation.
        let typeMatches ← liftTermElabM do
          let statement ← vc.toVCStatement.type
          Meta.isDefEq info.type statement
        if typeMatches then return true
  return false

/-- Check coverage before attempting the global induction. The ordinary VC
export remains useful after a partial check; no missing premise is admitted. -/
private def missingRequiredTheorems (mod : Module) : CommandElabM (Array Name) := do
  let mut missing := #[]
  let acts := #[(initializerName, false)] ++ mod.actions.map (fun proc =>
    (proc.name, proc.info.isTransition))
  for (act, nativeTransition) in acts do
    let noThrow := Name.mkSimple s!"{act}_doesNotThrow"
    unless ← theoremAvailable noThrow do missing := missing.push noThrow
    for inv in mod.invariants do
      unless (← theoremAvailable (preservationTheoremName act inv.name true)) ||
          (!nativeTransition && (← theoremAvailable (preservationTheoremName act inv.name false))) do
        missing := missing.push (preservationTheoremName act inv.name true)
  let env ← getEnv
  let ns ← getCurrNamespace
  for proc in mod.procedures do
    for marker in [`contract, `frame] do
      if env.contains (ns ++ proc.name ++ marker) then
        let certificateName := Name.mkSimple s!"{proc.name}_{marker}"
        unless ← theoremAvailable certificateName do
          missing := missing.push certificateName
  return missing

/-! ## Generation Context -/

private structure GenCtx where
  mod : Module
  substs : ReachableInvariantSubst
  /-- Implicit binders surrounding both the outer and projection theorems
  (sorts/userParams as implicit, typeclass instances as `[ ]`). -/
  binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  /-- Named-arg list `(ρ := Theory ⟨sorts⟩)(σ := State ⟨...⟩)(<sortName> := <subst>)…(χ := …)`
  used to instantiate the system-bound parameters at every call site. -/
  namedArgs : Array (TSyntax `Lean.Parser.Term.namedArgument)
  /-- The fully-applied `assembledRTS` term used in the theorem statement. -/
  rtsTerm : Term
  stateTerm : Term

/-- State-layout declarations depend only on sort and ordinary parameters. -/
private def mkUninterpretedApp (uninterpretedArgs : Array Term) (head : Name) :
    CommandElabM Term :=
  `(term| $(mkIdent head) $uninterpretedArgs*)

private def mkNamedArg (name : Name) (term : Term) :
    CommandElabM (TSyntax `Lean.Parser.Term.namedArgument) :=
  `(Lean.Parser.Term.namedArgument| ($(mkIdent name) := $term:term))

/-- Apply a head `name` to a mix of named and positional args. Lean's
quotation syntax can mix the two inside a `term|`, but only for a fixed
shape; for dynamically-sized arrays we hand-build the `Term.app` node. -/
private def mkAppWithNamedAndPositionalArgs
    (name : Name) (namedArgs : Array (TSyntax `Lean.Parser.Term.namedArgument))
    (positionalArgs : Array Term) : Term :=
  let args := namedArgs.map (·.raw) ++ positionalArgs.map (·.raw)
  ⟨mkNode `Lean.Parser.Term.app #[mkIdent name, mkNullNode args]⟩

/-- Explicit applications skip Lean's optional-argument scan of the result.
For a WP certificate that result contains the computed semantics of the action;
recursively telescoping it can expand an entire composed initializer. -/
private def mkExplicitCertificateApp
    (name : Name) (namedArgs : Array (TSyntax `Lean.Parser.Term.namedArgument))
    (positionalArgs : Array Term) : CommandElabM Term := do
  let head ← `(term| @$(mkIdent name))
  let mut args := namedArgs
  let supplied := namedArgs.filterMap fun arg => match arg with
    | `(Lean.Parser.Term.namedArgument| ($id:ident := $_:term)) => some id.getId
    | _ => none
  let info ← getConstInfo ((← getCurrNamespace) ++ name)
  let mut declType := info.type
  -- Preserve ordinary instance inference for declaration-specific dictionaries
  -- (for example, decidability of an ensure). Stop at the syntactic result:
  -- reducing it here would perform the very WP scan we are avoiding.
  while let .forallE binder _ body bi := declType do
    if !supplied.contains binder then
      if bi.isInstImplicit then
        args := args.push (← mkNamedArg binder (← `(term| inferInstance)))
      else if bi.isImplicit || bi.isStrictImplicit then
        args := args.push (← mkNamedArg binder (← `(term| _)))
    declType := body
  let appArgs := args.map (·.raw) ++ positionalArgs.map (·.raw)
  return ⟨mkNode `Lean.Parser.Term.app #[head.raw, mkNullNode appArgs]⟩

private def mkGenCtx (mod : Module) (substs : ReachableInvariantSubst) : CommandElabM GenCtx := do
  -- Binders: sorts/userParams become implicit; typeclass binders are kept
  -- unless a sort assumption is specialized away. User dictionaries remain
  -- explicit binders at the substituted type, preserving distinct slots.
  let binders ← mod.parameters.filterMapM fun p => do
    match p.kind with
    | .sort _ | .userParameter =>
        match ← binderSubst? substs p with
        | some b => some <$> mkImplicitBinder b
        | none => pure none
    | .moduleTypeclass .sortAssumption | .moduleTypeclass .userDefined =>
        binderSubst? substs p
    | _ => pure none
  -- Structural declarations carry only sorts and ordinary values.
  let uninterpretedArgs ← mod.parameters.filterMapM fun p => do
    match p.kind with
    | .sort _ | .userParameter => some <$> argSubst substs p
    | _ => pure none
  -- Concrete instantiations for the system-bound parameters (ρ, σ, χ).
  -- Inhabited instances are synthesized; user dictionaries are pinned.
  let theoryTerm ← mkUninterpretedApp uninterpretedArgs theoryName
  let fieldTerm ← mkUninterpretedApp uninterpretedArgs fieldAbstractDispatcherName
  let stateTerm ← `(term| $(mkIdent stateName) $fieldTerm)
  let rtsArgs ← mod.parameters.filterMapM fun p => do
    match p.kind with
    | .sort _ | .userParameter | .moduleTypeclass .sortAssumption |
        .moduleTypeclass .userDefined =>
        some <$> mkNamedArg p.name (← argSubst substs p)
    | _ => pure none
  let rtsTerm := mkAppWithNamedAndPositionalArgs assembledRTSName rtsArgs #[]
  let decEqArgs ← (mod.parameters.filter fun p =>
    p.kind == .moduleTypeclass .sortAssumption &&
      p.name.toString.endsWith "_dec_eq").mapM (argSubst substs)
  let rep ← `(term| @$(mkIdent instAbstractFieldRepresentationName):ident
    $uninterpretedArgs:term* $decEqArgs:term*)
  let lawful ← `(term| @$(mkIdent instLawfulAbstractFieldRepresentationName):ident
    $uninterpretedArgs:term* $decEqArgs:term*)
  -- Build the named-arg list: ρ, σ, each sort/userParam, χ.
  let mut namedArgs := #[
    ← mkNamedArg environmentTheoryName theoryTerm,
    ← mkNamedArg environmentStateName stateTerm,
    ← mkNamedArg environmentSubTheoryName (← `(term| $(mkIdent ``instIsSubReaderOfRefl))),
    ← mkNamedArg environmentSubStateName (← `(term| $(mkIdent ``instIsSubStateOfRefl))),
    ← mkNamedArg fieldRepresentationName rep,
    ← mkNamedArg lawfulFieldRepresentationName lawful]
  for p in mod.parameters do
    match p.kind with
    | .sort _ | .userParameter | .moduleTypeclass .userDefined |
        .moduleTypeclass .sortAssumption =>
        namedArgs := namedArgs.push (← mkNamedArg p.name (← argSubst substs p))
    | _ => pure ()
  namedArgs := namedArgs.push (← mkNamedArg fieldConcreteTypeName fieldTerm)
  return { mod, substs, binders, namedArgs, rtsTerm, stateTerm }

/-- Apply `head` (e.g. `assembledInvariantsName` or an individual `invName`)
to the system-bound named args, then to `th` and `st`, as a 2-arg predicate
`fun th st => @head <namedArgs>* th st`. -/
private def GenCtx.mkInvariantPredicate (ctx : GenCtx) (head : Name) : CommandElabM Term := do
  let th := mkIdent `th
  let st := mkIdent `st
  let body := mkAppWithNamedAndPositionalArgs head ctx.namedArgs
    #[(⟨th⟩ : Term), (⟨st⟩ : Term)]
  `(term| fun $th:ident $st:ident => $body)

/-! ## Preservation Proof Arms -/

/-- A successful WP certificate gives the same successful transition
preservation certificate. This does not rerun a solver or unfold the body. -/
private def GenCtx.mkTrProof (ctx : GenCtx) (actName invName : Name)
    (positional : Array Term) : CommandElabM Term := do
  let trName := preservationTheoremName actName invName true
  if ← theoremAvailable trName then
    return ← mkExplicitCertificateApp trName ctx.namedArgs positional
  let wpName := preservationTheoremName actName invName false
  let wpApp ← mkExplicitCertificateApp wpName ctx.namedArgs positional
  let act := mkAppWithNamedAndPositionalArgs (toExtName actName) ctx.namedArgs positional
  let derivedEq := mkAppWithNamedAndPositionalArgs
    (toDerivedEqName (toExtName actName)) ctx.namedArgs positional
  `(term| by
    let hact := $act
    have checked := $wpApp
    -- A bare proof name also triggers the optional-argument scan.
    exact $(mkIdent ``VeilM.meetsSpecificationIfSuccessfulAssuming_toTransition)
      (m := $(mkIdent ``Mode.external)) hact $derivedEq (@checked))

private def mkInitArm (ctx : GenCtx) (invName : Name) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let hpresApp ← ctx.mkTrProof initializerName invName (positional := #[])
  `(tacticSeq|
    have hpres := $hpresApp
    exact hpres th default s ⟨has, trivial⟩ hinit)

private def mkActionArm
    (ctx : GenCtx) (actName invName : Name) (actionArgs : Array Ident) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let positional := actionArgs.map fun id => (⟨id⟩ : Term)
  let hpresApp ← ctx.mkTrProof actName invName (positional := positional)
  let native := (ctx.mod.actions.find? (·.name == actName)).any (·.info.isTransition)
  let rawStep := mkIdent `hraw
  let convert ← match native with
    | true => do
      let rawName := toTransitionName (toExtName actName)
      let raw := mkAppWithNamedAndPositionalArgs rawName ctx.namedArgs positional
      let ext := mkIdent (toExtName actName)
      let body := mkIdent (toDoName actName)
      `(tactic|
        have $rawStep:ident : $raw th s s' := by
          apply $(mkIdent ``Transition.toVeilM_toTransitionDerived_sound)
            (m := $(mkIdent ``Mode.external)) (small := $(ctx.stateTerm))
            (lens := $(mkIdent ``instIsSubStateOfRefl)) $raw th s s'
          simpa only [$(mkIdent ``VeilM.toTransitionDerived):ident,
            $(mkIdent ``VeilSpecM.toTransitionDerived):ident,
            $(mkIdent ``Transition.toVeilM):ident,
            $(mkIdent ``VeilM.returnUnit):ident, $ext:ident, $body:ident,
            $(mkIdent rawName):ident, $(mkIdent ``Loom.Cont.inv):ident,
            $(mkIdent ``Loom.Order.compl):ident,
            $(mkIdent ``instIsSubStateOfRefl):ident,
            $(mkIdent ``IsSubStateOf.getFrom):ident,
            $(mkIdent ``IsSubStateOf.setIn):ident, substateSimp, wpSimp] using htr)
    | false => `(tactic| skip)
  let stepProof ← match native with
    | true => `(tactic| exact $rawStep:ident)
    | false => `(tactic| exact htr)
  `(tacticSeq|
    have hpres := $hpresApp
    $convert:tactic
    exact hpres th s s' ⟨has, ih⟩ (by
      simp only [nextSimp]
      $stepProof:tactic))

/-- Combine per-invariant arms into a right-nested conjunction proof,
matching the layout of `repeatedAnd` in `assembleAssertions`. -/
private def mkConjunctionProof
    (proofs : Array (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if proofs.isEmpty then return ← `(tacticSeq| trivial)
  proofs.pop.foldrM (init := proofs.back!) fun p acc =>
    `(tacticSeq|
      constructor
      · ($p:tacticSeq)
      · ($acc:tacticSeq))

/-! ## Step Case (action induction) -/

private def mkActionCaseAlt (ctx : GenCtx) (act : ProcedureSpecification) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.inductionAlt) := do
  -- Action parameter names can coincide with the induction's state/theory
  -- binders. Constructor cases need only positional arguments here.
  let actionArgs := act.params.mapIdx fun i _ =>
    mkVeilImplementationDetailIdent (Name.mkSimple s!"reachable_arg_{i}")
  let arms ← ctx.mod.invariants.mapM fun inv => mkActionArm ctx act.name inv.name actionArgs
  let conjunction ← mkConjunctionProof arms
  let conjunctionTac ← `(tactic| ($conjunction:tacticSeq))
  `(Lean.Parser.Tactic.inductionAlt|
    | $(mkIdent act.name):ident $actionArgs:ident* =>
        simp only [nextSimp] at htr
        unfold $(mkIdent assembledInvariantsName):ident
        $conjunctionTac:tactic)

private def mkActionCasesTactic (ctx : GenCtx) : CommandElabM (TSyntax `tactic) := do
  let alts ← ctx.mod.actions.mapM (mkActionCaseAlt ctx)
  `(tactic| cases label with $[$alts]*)

/-! ## Outer Theorem -/

private def mkReachableInvariantsTheorem (ctx : GenCtx) : CommandElabM Command := do
  let initArms ← ctx.mod.invariants.mapM fun inv => mkInitArm ctx inv.name
  let initConjunction ← mkConjunctionProof initArms
  let initConjunctionTac ← `(tactic| ($initConjunction:tacticSeq))
  let actionCases ← mkActionCasesTactic ctx
  let invPredicate ← ctx.mkInvariantPredicate assembledInvariantsName
  let thmName := mkIdent generatedInvariantsTheoremName
  let binders := ctx.binders
  let rtsTerm := ctx.rtsTerm
  `(command|
    open Classical in
    theorem $thmName $[$binders]* :
        $(mkIdent ``RelationalTransitionSystem.isInvariant) $rtsTerm $invPredicate := by
      intro th st hr
      induction hr with
      | init s has hinit =>
          unfold $(mkIdent assembledInvariantsName):ident
          $initConjunctionTac:tactic
      | step s s' hreach hnext ih =>
          have has := $(mkIdent ``RelationalTransitionSystem.reachable_assumptions) _ _ _ hreach
          rcases hnext with ⟨label, htr⟩
          $actionCases:tactic)

/-! ## Projection Theorems -/

private def mkProjectionDestructProof (mod : Module) (invName : Name) :
    CommandElabM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  if mod.invariants.size == 1 then
    `(tacticSeq| exact h)
  else
    -- Two instances can have invariants with the same final name. Index the
    -- conjunction's binders instead of deriving names from that final name.
    let hNames := mod.invariants.mapIdx fun i _ =>
      mkVeilImplementationDetailIdent (Name.mkSimple s!"reachable_invariant_{i}")
    let some targetIndex := mod.invariants.findIdx? (·.name == invName)
      | throwError "unknown reachable-invariant projection {invName}"
    let hTarget := hNames[targetIndex]!
    `(tacticSeq|
      rcases h with ⟨ $[$hNames],* ⟩
      exact $hTarget:ident)

private def mkProjectionTheorem (ctx : GenCtx) (invName : Name) : CommandElabM Command := do
  let thmName := mkIdent (invName ++ `is_inv)
  let invPredicate ← ctx.mkInvariantPredicate invName
  let destructProof ← mkProjectionDestructProof ctx.mod invName
  let destructTac ← `(tactic| ($destructProof:tacticSeq))
  let binders := ctx.binders
  let rtsTerm := ctx.rtsTerm
  let outerArgs ← ctx.mod.parameters.filterMapM fun p => do
    match p.kind with
    | .sort _ =>
        if ctx.substs.contains p.name then return none
        return some (← mkNamedArg p.name (← p.arg))
    | .moduleTypeclass .sortAssumption =>
        if mentionsSubstitution ctx.substs p.type then return none
        return some (← mkNamedArg p.name (← p.arg))
    | .userParameter | .moduleTypeclass .userDefined =>
        return some (← mkNamedArg p.name (← p.arg))
    | _ => return none
  let outerProof := mkAppWithNamedAndPositionalArgs generatedInvariantsTheoremName
    outerArgs #[(← `(term| th)), (← `(term| st)), (← `(term| hr))]
  `(command|
    open Classical in
    theorem $thmName $[$binders]* :
        $(mkIdent ``RelationalTransitionSystem.isInvariant) $rtsTerm $invPredicate := by
      intro th st hr
      have h := $outerProof:term
      unfold $(mkIdent assembledInvariantsName):ident at h
      $destructTac:tactic)

/-! ## Entry Points -/

private def existingReachableTheorem (ctx : GenCtx) (name predicate : Name) :
    CommandElabM Bool := do
  let fullName := (← getCurrNamespace) ++ name
  let some info ← withoutExporting do return (← getEnv).find? fullName
    | return false
  let binders := ctx.binders
  let rts := ctx.rtsTerm
  let inv ← ctx.mkInvariantPredicate predicate
  let expectedStx ← `(term| open Classical in forall? $binders*,
    $(mkIdent ``RelationalTransitionSystem.isInvariant) $rts $inv)
  let typeMatches ← liftTermElabM <| Term.withoutErrToSorry do
    let expected ← Term.elabType expectedStx
    Term.synthesizeSyntheticMVarsNoPostponing
    Meta.isDefEq info.type (← instantiateMVars expected)
  unless typeMatches do
    throwError "cannot generate reachable-invariant theorem `{fullName}` because a declaration with that name already exists with a different type or sort substitution"
  if let .thmInfo thm := info then
    if thm.value.hasSyntheticSorry then
      throwError "reachable-invariant theorem `{fullName}` has an unfinished proof"
  unless veil.smt.trust.get (← getOptions) do
    if (← collectAxioms fullName).contains ``sorryAx then
      throwError "cannot reuse reachable-invariant theorem `{fullName}` because its proof depends on sorryAx while veil.smt.trust is false"
  return true

/-- Command elaboration normally recovers from a failing tactic with a
synthetic sorry. Reachability certificates must be installed atomically:
discard the recovered declaration and skip projections if checking fails. -/
private def elabCheckedReachableTheorem (name : Name) (command : Command) :
    CommandElabM Bool := do
  let savedEnv ← getEnv
  try
    elabCommand command
    let info? ← withoutExporting do
      return (← getEnv).find? ((← getCurrNamespace) ++ name)
    let valid := match info? with
      | some (.thmInfo info) =>
          !info.value.hasMVar && !info.value.hasFVar && !info.value.hasSyntheticSorry
      | _ => false
    unless valid do
      setEnv savedEnv
    if valid && !veil.smt.trust.get (← getOptions) then
      let fullName := (← getCurrNamespace) ++ name
      if (← collectAxioms fullName).contains ``sorryAx then
        setEnv savedEnv
        throwError "cannot export reachable-invariant theorem `{fullName}` because its proof depends on sorryAx while veil.smt.trust is false"
    return valid
  catch ex =>
    setEnv savedEnv
    throw ex

def Module.generateReachableInvariantTheorems
    (mod : Module) (substs : ReachableInvariantSubst) : CommandElabM Unit :=
  -- These proofs are finite structural induction over already checked VCs.
  -- Their normalization work grows with the concrete product's field and
  -- invariant counts; do not inherit the per-solver heartbeat allowance.
  withScope (fun scope => { scope with
    opts := (scope.opts.set `maxHeartbeats (0 : Nat)).setBool `Elab.async false }) do
    mod.throwIfSpecNotFinalized
    validateReachableInvariantSubstitutions mod substs
    let missing ← missingRequiredTheorems mod
    unless missing.isEmpty do
      logWarning m!"#gen_theorems exported available local lemmas, but omitted reachable-invariant theorems: missing proof obligations {missing.toList}"
      return
    let ctx ← mkGenCtx mod substs
    unless ← existingReachableTheorem ctx generatedInvariantsTheoremName assembledInvariantsName do
      unless ← elabCheckedReachableTheorem generatedInvariantsTheoremName
          (← mkReachableInvariantsTheorem ctx) do
        return
    for inv in mod.invariants do
      unless ← existingReachableTheorem ctx (inv.name ++ `is_inv) inv.name do
        unless ← elabCheckedReachableTheorem (inv.name ++ `is_inv)
            (← mkProjectionTheorem ctx inv.name) do
          return

def parseTheoremSortSubstitutions (stx : Syntax) : CommandElabM ReachableInvariantSubst := do
  match stx with
  | `(command| #gen_theorems) =>
      pure {}
  | `(command| #gen_theorems with $substs:theoremSortSubstitution,*) =>
      parseReachableInvariantSubstitutions substs
  | _ => throwUnsupportedSyntax

end Veil
