module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Solver
public import Veil.Core.Tools.Synthesizer.Soundness

/-!
# The safety certificate

At a fixpoint the search has clauses `c₁ … cₖ` such that `Inv = p₁ ∧ … ∧ pₘ ∧ c₁ ∧ … ∧ cₖ`, where
`P = p₁ ∧ … ∧ pₘ` is the property, is inductive. This file proves, in the module's namespace,

    theorem Mod.ic3_safe : ∀ sorts [insts] th st,
      (Mod.relationalTransitionSystem sorts).reachable th st → Mod.ic3_prop sorts th st

## Main definitions

* `Veil.Synthesizer.certify`: build and check the safety certificate.
* `Veil.Synthesizer.proveObligation`: prove one obligation from a fresh solver answer.
* `Veil.Synthesizer.CertificateResult`: the theorem a certificate added, and its axioms.

## Implementation notes

* For each conjunct `q` of `Inv`, the initiation and consecution queries are asked again with
  proof reconstruction, and their proofs become the theorems `Mod.ic3_init_i` and `Mod.ic3_cons_i`
  once the kernel accepts them (`addCheckedDecl`). A consecution theorem is stated with the
  normalized transition relation; when its proof replays only from the statement written with
  `tr`, it is `Mod.ic3_cons_i_tr`. A step no form replays is taken on the solver's word as
  `Mod.ic3_init_i_trusted` or `Mod.ic3_cons_i_trusted`, and the command reports `sorryAx`.
* `Mod.ic3_inv` and `Mod.ic3_prop` are the conjunctions of the wrapped predicates, and `ic3_safe`
  applies `RelationalTransitionSystem.invariant_of_inductive` and `Invariant.mono`. Consecution
  matches on the label: each action's case instantiates the queries' `ActionTag` with the module's
  tag type and rewrites `tr` to the normalized relation along `Mod.ic3_tr_eq_norm`.
* The transition system is Veil's `relationalTransitionSystem`: its initial states run `after_init`
  from the default state, and it does not assume `trusted invariant`s.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Command Term Meta Veil Lean.Parser.Term

/-- The axioms a fully checked development rests on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The theorem a certificate added. -/
structure CertificateResult where
  /-- `ic3_safe` or `ic3_unsafe`. -/
  theoremName : Name
  /-- The predicate the theorem is about: `ic3_inv` for safety, `ic3_prop` for a refutation. -/
  strengtheningName : Name
  /-- The axioms the theorem depends on. -/
  axioms : Array Name
  /-- Whether every axiom is standard. -/
  kernelChecked : Bool
  /-- The axioms that are not standard. -/
  offenders : Array Name

/-- The result for a theorem in the environment. -/
def certificateResult (theoremName strengtheningName : Name) : CoreM CertificateResult := do
  let axioms ← collectAxioms theoremName
  let offenders := axioms.filter (!standardAxioms.contains ·)
  return { theoremName, strengtheningName, axioms, kernelChecked := offenders.isEmpty, offenders }

/-- Fail when a declaration of a certificate is in the environment: a module holds one. -/
def throwIfCertified (mod : Veil.Module) (names : List Name) : CommandElabM Unit := do
  for n in names do
    if (← getEnv).contains (mod.name ++ n) then
      throwError "IC3 certificate: {mod.name ++ n} is already declared; a module can hold one \
        certificate, so run `#synthesize_invariants … certify` once per module"

/-- `liftTermElabM` without the command's heartbeat limit. -/
def liftUnbounded (x : TermElabM α) : CommandElabM α :=
  liftTermElabM <| withTheReader Core.Context (fun c ↦ { c with maxHeartbeats := 0 }) x

/-- Elaborate a generated command synchronously and without a heartbeat limit, and fail if it
logged an error. -/
def elabChecked (c : TSyntax `command) : CommandElabM Unit := do
  let errors : CommandElabM Nat :=
    return ((← get).messages.toList.filter (·.severity == .error)).length
  let before ← errors
  elabCommand (← `(command| set_option $(mkIdent `Elab.async):ident false in
    set_option $(mkIdent `maxHeartbeats):ident 0 in $c))
  if (← errors) > before then
    throwError "IC3 certificate: a generated declaration failed to elaborate (see the errors above)"

/-- An identifier no name of the module can capture. -/
def freshIdent (n : Name) : CommandElabM Ident := return mkIdent (← liftCoreM (mkFreshUserName n))

/-! ### Proof terms -/

/-- A proof of disjunct `k` of a right-nested disjunction of `n` from a proof `h` of it. -/
def orIntro (k n : Nat) (h : Term) : TermElabM Term := do
  if n ≤ 1 then return h
  let mut t ← if k + 1 == n then pure h else `(Or.inl $h)
  for _ in [:k] do t ← `(Or.inr $t)
  return t

/-- The projection `h.2.….2.1` of conjunct `i` of a right-nested conjunction of `n`. -/
def andProj (h : Term) (i n : Nat) : TermElabM Term := do
  let mut t := h
  for _ in [:i] do t ← `(($t).2)
  if i + 1 < n then t ← `(($t).1)
  return t

/-- The anonymous constructor `⟨t₀, t₁, …⟩`, `t₀` for one term, `True.intro` for none. -/
def anonymousTuple : Array Term → TermElabM Term
  | #[] => `(True.intro)
  | #[t] => pure t
  | ts => `(⟨$ts,*⟩)

/-! ### Obligations -/

/-- Add a proof of a closed statement as a theorem, checked by the kernel first. -/
def addProofTheorem (name : Name) (ty pf : Expr) : MetaM Unit := do
  addCheckedDecl <| .thmDecl ⟨⟨name, [], ← instantiateMVars ty⟩, ← instantiateMVars pf, [name]⟩

/-- `sorryAx ty false`, a proof of `ty` the kernel accepts whatever `ty` is. -/
def admittedProof (ty : Expr) : Expr :=
  mkApp2 (mkConst ``sorryAx [Level.zero]) ty (mkConst ``Bool.false)

/-- Add `pf`, a proof taken on the solver's word, as the theorem `name : ty`. When the kernel
rejects `pf`, the statement is admitted outright and the kernel's message returned. -/
def addTrustedTheorem (name : Name) (ty pf : Expr) : CommandElabM (Option String) := do
  try
    liftUnbounded <| addProofTheorem name ty pf
    return none
  catch e =>
    liftUnbounded <| addProofTheorem name ty (admittedProof ty)
    return some ((← e.toMessageData.toString).take 160).toString

/-- Ask a certificate query without a model. An answer the solver gave up on is asked once more
with twice the timeout. -/
def runCertificateQuery (mod : Veil.Module) (stmt : Term) (steps : Nat) :
    TermElabM QueryResult := do
  let (r, _) ← runStatement mod stmt steps (wantModel := false)
  let .unknown reason := r | return r
  unless r.solverGaveUp do return r
  let t := veil.smt.timeout.get (← getOptions)
  logInfo s!"IC3 certificate: a query returned unknown ({reason.take 160}); asking again with \
    veil.smt.timeout {2 * t}"
  withOptions (veil.smt.timeout.set · (2 * t)) do
    return (← runStatement mod stmt steps (wantModel := false)).1

/-- Prove the obligation `what` and add it as the theorem `name`; return the theorem's name and
whether its statement is the one written with `tr`.

The statement `stmt plainTr` is asked with reconstruction. With `twoForms`, a proof that does not
replay from the statement written with the normalized transition relation is tried from the one
written with `tr`, as `name_tr`. When no form replays, the solver's answer is taken on its word as
`name_trusted`, with a warning. A `sat` answer, or no verdict without a trusted proof in hand, is
an error. -/
def proveObligation (mod : Veil.Module) (name : Name) (stmt : (plainTr : Bool) → TermElabM Term)
    (twoForms : Bool) (steps : Nat) (what : String) : CommandElabM (Name × Bool) := do
  let ask (plainTr trust : Bool) : CommandElabM QueryResult :=
    liftUnbounded <| withOptions (veil.synthesizer.trust.set · trust) do
      runCertificateQuery mod (← stmt plainTr) steps
  let formNote (plainTr : Bool) : String :=
    if !twoForms then ""
    else if plainTr then " in the plain form of the statement"
    else " in the normalized form of the statement"
  let noProof (plainTr : Bool) : QueryResult → String
    | .sat _ | .satUndecoded _ =>
      s!"IC3 certificate: {what} did not hold at the fixpoint{formNote plainTr}"
    | .unknown reason =>
      s!"IC3 certificate: the solver could not decide {what}{formNote plainTr} ({reason})"
    | .error e => s!"IC3 certificate: the query for {what}{formNote plainTr} could not be posed or \
        its answer read ({e})"
    | .unsat .. => ""
  let forms := #[(false, name)] ++ if twoForms then #[(true, name.appendAfter "_tr")] else #[]
  let mut failures : Array String := #[]
  -- A trusted proof from a form that did not replay, for the `_trusted` theorem.
  let mut onFaith : Option (Expr × Expr × Bool) := none
  for (plainTr, thmName) in forms do
    match ← ask plainTr false with
    | .unsat ty pf true =>
      failures :=
        failures.push s!"lean-smt could not reconstruct the solver's proof{formNote plainTr}"
      onFaith := some (ty, pf, plainTr)
    | .unsat ty pf false =>
      try
        liftUnbounded <| addProofTheorem thmName ty pf
        if plainTr then
          logInfo m!"IC3 certificate: {what} was replayed{formNote plainTr} after the first \
            attempt failed ({"; ".intercalate failures.toList})"
        return (thmName, plainTr)
      catch e =>
        failures := failures.push s!"the kernel rejected the replayed proof{formNote plainTr} \
          ({((← e.toMessageData.toString).take 160).toString})"
    | r@(.sat _) | r@(.satUndecoded _) => throwError (noProof plainTr r)
    | r =>
      -- No verdict: only a trusted proof of the other form still supports the obligation.
      if onFaith.isNone then throwError (noProof plainTr r)
      failures := failures.push s!"no verdict{formNote plainTr} ({r})"
  let (ty, pf, plainTr) ← match onFaith with
    | some t => pure t
    | none =>
      -- Every form was rejected by the kernel: ask once more, trusting the solver.
      match ← ask false true with
      | .unsat ty pf _ => pure (ty, pf, false)
      | r => throwError (noProof false r)
  let trustedName := name.appendAfter "_trusted"
  if let some rejection ← addTrustedTheorem trustedName ty pf then
    failures := failures.push s!"the kernel rejected the partially reconstructed proof as well \
      ({rejection}), so the statement is admitted outright"
  logWarning m!"IC3 certificate: {what} is taken on the solver's word: \
    {"; ".intercalate failures.toList}"
  return (trustedName, plainTr)

/-- Define `name sorts [insts] : Theory → State → Prop` as the conjunction of the predicates. -/
def definePredicate (ctx : QueryCtx) (name : Ident) (conjuncts : Array Term) :
    CommandElabM Unit := do
  let (th, st) := (mkIdent `th, mkIdent `st)
  let body ← liftTermElabM do
    repeatedAnd (← conjuncts.mapM fun t ↦ do `($(← ctx.wrapPred t) $th $st))
  elabChecked (← `(command| def $name $(ctx.sortBinders ++ ctx.typeclassBinders)* :
    $(ctx.theoryT) → $(ctx.stateT) → Prop := fun $th $st ↦ $body))

/-! ### The certificate -/

/-- The proof that every action preserves `Inv`: a match on the label whose case for action `k`
instantiates the consecution theorems `consNames` at that action. `consPlain[i]` says that theorem
`i` is stated with `tr`; the others are stated with the normalized relation, and the transition
hypothesis is rewritten along `trEq`. -/
def consecutionProof (mod : Veil.Module) (ctx : QueryCtx) (consNames : Array Name)
    (consPlain : Array Bool) (trEq? : Option Ident) (has s s' lbl htr hInv : Ident) :
    CommandElabM Term := do
  let n := consNames.size
  let tagType := Ident.toEnumConcreteType actionTagType
  let arities ← liftTermElabM <| mod.actions.mapM fun act ↦ do
    return (← mod.declarationAllParams act.name act.declarationKind).2.size
  if mod.actions.isEmpty then return ← `(nomatch $lbl)
  let hInvs ← liftTermElabM <| (Array.range n).mapM (andProj hInv · n)
  let alts ← mod.actions.mapIdxM fun k act ↦ do
    let args ← (Array.range arities[k]!).mapM (freshIdent <| .mkSimple s!"a{·}")
    let ctor := mkIdent (labelTypeName ++ act.name)
    liftTermElabM do
      -- The queries quantify over the arguments of every action: this action's fill its slots,
      -- and the others take `default`.
      let mut allArgs : Array Term := #[]
      for k' in [:mod.actions.size] do
        if k' == k then allArgs := allArgs ++ args.map (·)
        else for _ in [:arities[k']!] do allArgs := allArgs.push (← `(default))
      let proofs ← (Array.range n).mapM fun i ↦ do
        let step : Term ← match trEq? with
          | some trEq =>
            if consPlain[i]! then pure htr
            else `(Eq.mp ($trEq $(ctx.sorts)* $(ctx.th) $s ($ctor $args*) $s') $htr)
          | none => pure htr
        `(Classical.byContradiction fun hc ↦ $(mkIdent consNames[i]!) $(ctx.sorts)* $tagType
            inferInstance $(mkIdent (tagType.getId ++ act.name)) $allArgs* $(ctx.th) $s $s'
            ⟨$has, $hInvs,*, $(← orIntro k mod.actions.size (← `(⟨rfl, $step⟩))), hc⟩)
      let pat : Term ← if args.isEmpty then pure ctor else `($ctor $args*)
      `(matchAltExpr| | $pat, $htr => $(← anonymousTuple proofs))
  `(match $lbl:ident, $htr:ident with $alts:matchAlt*)

/-- Build and check the safety certificate for the clauses of a fixpoint frame. -/
def certify (mod : Veil.Module) (property : Array Term) (clauses : Array Clause) :
    CommandElabM CertificateResult := do
  throwIfCertified mod [`ic3_init_0, `ic3_prop, `ic3_safe]
  let ctx ← liftTermElabM (QueryCtx.ofModule mod)
  let conj := property ++ (← liftTermElabM (clauses.mapM (·.toTerm)))
  let n := conj.size
  let trNorm? ← liftUnbounded (TrNorm.ensure ctx)
  -- The obligations, from fresh solver answers.
  let obligationName (kind : String) (i : Nat) : Name := mod.name ++ .mkSimple s!"ic3_{kind}_{i}"
  let mut initNames := #[]
  let mut consNames := #[]
  let mut consPlain := #[]
  for i in [:n] do
    let q := conj[i]!
    let (init, _) ← proveObligation mod (obligationName "init" i)
      (fun _ ↦ ctx.statement none { init := true, goal := .violates q }) false 0
      s!"initiation of conjunct {i}"
    let (cons, plainTr) ← proveObligation mod (obligationName "cons" i)
      (fun plainTr ↦ ctx.statement (if plainTr then none else trNorm?)
        { frame := conj, separate := true, steps := 1, goal := .violates q })
      trNorm?.isSome 1 s!"consecution of conjunct {i}"
    initNames := initNames.push init
    consNames := consNames.push cons
    consPlain := consPlain.push plainTr
  let (invName, propName) := (mkIdent `ic3_inv, mkIdent `ic3_prop)
  definePredicate ctx invName conj
  definePredicate ctx propName property
  -- The proof of `ic3_safe`, over fresh binders that no name of the module can capture.
  let (th, st) := (mkIdent `th, mkIdent `st)
  let [has, s, s', lbl, htr, hinit, hInv] ←
      [`has, `s, `s', `lbl, `htr, `hinit, `hInv].mapM freshIdent
    | unreachable!
  let sorts := ctx.sorts
  let initProof ← liftTermElabM do
    anonymousTuple (← initNames.mapM fun thm ↦
      `(Classical.byContradiction fun hc ↦ $(mkIdent thm) $sorts* $th $s ⟨$has, $hinit, hc⟩))
  let trEq? := trNorm?.map fun _ ↦ mkIdent (TrNorm.eqName mod)
  let consProof ← consecutionProof mod ctx consNames consPlain trEq? has s s' lbl htr hInv
  let propProof ← liftTermElabM do
    anonymousTuple (← (Array.range property.size).mapM (andProj hInv · n))
  let rts ← `($assembledRTS $sorts*)
  let thmName := mkIdent `ic3_safe
  elabChecked (← `(command|
    theorem $thmName $(ctx.sortBinders ++ ctx.typeclassBinders)* : ∀ ($th : $(ctx.theoryT))
        ($st : $(ctx.stateT)), ($rts).$(mkIdent `reachable) $th $st → $propName $sorts* $th $st :=
      (Veil.RelationalTransitionSystem.invariant_of_inductive (sys := $rts) (p := $invName $sorts*)
        (fun $th $s $has $hinit ↦ $initProof)
        (fun $th $s $lbl $s' $has $hInv $htr ↦ $consProof)).mono (q := $propName $sorts*)
        (fun $th $st $hInv ↦ $propProof)))
  liftCoreM <| certificateResult (mod.name ++ thmName.getId) (mod.name ++ invName.getId)

end Veil.Synthesizer
