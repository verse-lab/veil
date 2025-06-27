import Lean
import Lean.Parser
import Veil.Util.Meta
import Veil.Util.DSL
import Veil.Model.TransitionSystem
import Veil.DSL.Specification.SpecDef
import Veil.Theory.Basic
import Plausible

open Lean Lean.Elab.Command Lean.Meta Lean.Elab.Term

def deriveGen (inductiveTypeStx : Term) : TermElabM Syntax := do
  let inductiveTypeTerm <- elabTerm inductiveTypeStx none
  let .some inductiveType := inductiveTypeTerm.getAppFn.constName?
    | throwError "{inductiveTypeStx} is not an inductive type"
  let env ← getEnv
  let .some inductiveTypeConst := env.find? inductiveType
    | throwError "inductive type {inductiveType} not found"
  unless inductiveTypeConst.isInductive do
    throwError "inductive type {inductiveType} is not an inductive type"
  let inductiveInfo := inductiveTypeConst.inductiveVal!
  let ctorsNum := inductiveInfo.numCtors
  -- let mut matchAlts := #[]
  let mut ctorNames := #[]
  let mut nums := #[]
  let mut sampleArgs := #[]
  for i in [0:ctorsNum] do
    nums := nums.push $ <- `(term| $(Syntax.mkNatLit i):term)
    let ctorName := inductiveInfo.ctors[i]!
    let .some (.ctorInfo ctorInfo) := env.find? ctorName | throwError "ctor {ctorName} not found"
    ctorNames := ctorNames.push $ mkIdent ctorName
    let ctorNumber := ctorInfo.numFields
    let mut sampleArg := #[]
    for _ in [0:ctorNumber] do
      sampleArg := sampleArg.push $ <- `(term| (<- Plausible.SampleableExt.interpSample _))
    sampleArgs := sampleArgs.push $ sampleArg
  `(command| def  $(mkIdent $ inductiveType ++ `gen) :
     Plausible.Gen $inductiveTypeStx := do
        match <- Plausible.Gen.chooseAny (Fin $(Syntax.mkNatLit ctorsNum):term) with
        $[| Fin.mk $nums _ => return $ctorNames $sampleArgs* ]*)

elab "#deriveGen" t:term : command => do
  let stx <- runTermElabM (fun _ => deriveGen t)
  elabCommand stx

open Plausible

variable [sys : RelationalTransitionSystem ρ σ] [Inhabited σ]
variable {labType : Type} (genL : Gen labType)
variable (nextComp : labType -> VeilExecM .external ρ σ Unit)
variable (next_refine : ∀ (rd : ρ) (st st' : σ) (l : labType),
  (nextComp l).operational rd st st' (Except.ok ()) <->
  sys.next rd st st')
variable (r₀ : ρ) (s₀ : σ) (hinit : sys.init r₀ s₀)

def random_transition (s : σ) : Gen (DivM (Except ExId σ)) := do
  let l <- genL
  return match nextComp l |>.run r₀ s with
    | .res (.ok ⟨_, s'⟩) => .res (.ok s')
    | .res (.error e) => .res (.error e)
    | .div => .div

attribute [spec low] Gen.wp_rand


-- def generateWPStep' : Elab.Tactic.TacticM Unit := Elab.Tactic.withMainContext do
--   let goalType <- Elab.Tactic.getMainTarget
--   let_expr WPGen _m _mInst _α _l _lInst _mPropInst x := goalType | throwError "{goalType} is not a WPGen"
--   let spec <- findSpec x
--   dbg_trace "spec: {spec.1}"
--   match spec with
--   | (spec, .wpgen) =>
--     Elab.Tactic.evalTactic $ <- `(tactic| apply $spec)
--   | (spec, .triple) =>
--     Elab.Tactic.evalTactic $ <- `(tactic|
--       eapply $(mkIdent ``WPGen.spec_triple);
--       apply $spec
--       )


-- elab "wpgen_app'" : tactic => generateWPStep'

include next_refine
omit [Inhabited σ] in
@[spec]
lemma random_transition_spec (s : σ) :
  triple
    ⌜sys.reachable r₀ s⌝
    (random_transition genL nextComp r₀ s)
    (fun
      | .res (.ok s') => ⌜sys.reachable r₀ s'⌝
      | _ => ⊤) := by sorry
  -- simp [random_transition]
  -- mwp; intros; split <;> simp
  -- expose_names; apply RelationalTransitionSystem.reachable.step _ _ h
  -- simp [ReaderT.run] at heq
  -- apply next_refine; simp [VeilExecM.operational]
  -- rw [heq]




structure RandomTrace (σ : Type) where
  trace : Array σ
  thrownException? : Option ExId
  numberOfSteps : Nat
  safe? : Bool

def check_safety (steps : Nat) (cfg : Configuration) [∀ r s, Testable (sys.safe r s)] : Gen (RandomTrace σ) := do
  let mut trace : RandomTrace σ := ⟨#[s₀], .none, 0, true⟩
  for _st in [0:steps]
  invariant ⌜ sys.reachable r₀ trace.trace.back!⌝
  invariant ⌜sys.inv r₀ trace.trace.back! -> trace.safe? = true⌝
  do
    let step ← random_transition genL nextComp r₀ trace.trace.back!
    match step with
    | .res (.ok s') =>
      match <- Testable.runProp (sys.safe r₀ s') cfg true with
      | .success _ | .gaveUp _ =>
        trace := { trace with trace := trace.trace.push s', numberOfSteps := trace.numberOfSteps + 1 }
      | .failure _ _ _ => break
    | .res (.error e) =>
      trace := { trace with thrownException? := e, safe? := true }
      break
    | .div => pure ()
  return trace

#check Elab.Tactic.allGoals

lemma check_safety_triple (size : Nat) (steps : Nat) (cfg : Configuration) [∀ r s, Testable (sys.safe r s)] :
  sys.isInvariant sys.safe ->
  triple ⌜sys.assumptions r₀ ∧ sys.init r₀ s₀⌝
  (check_safety genL nextComp r₀ s₀ steps cfg)
  (fun res => ⌜res.safe? = true⌝) := by
  intro sf
  dsimp [check_safety]
  wpgen_intro
  wpgen_step; wpgen_step; wpgen_step; wpgen_step
  { rename_i a; rcases a with ((_|_)|_) <;> dsimp
    wpgen_step; wpgen_step; wpgen_step
    { rename_i a; rcases a <;> dsimp <;> repeat' wpgen_step }
    repeat' wpgen_step }
  wpgen_step
  simp only [loomWpSimp, loomLogicSimp, invariants, List.foldr, id]
  constructor
  { intro s inv₁ inv₂; constructor; assumption
    rintro ((ex|_)|_) <;> simp
    {  } }





lemma check_safety_sound (size : Nat) (steps : Nat) (cfg : Configuration) [∀ r s, Testable (sys.safe r s)] :
  (ReaderT.run (check_safety genL nextComp r₀ s₀ steps cfg) ⟨size⟩ |>.run seed).1.safe? = false ->
  ¬ sys.isInvariant sys.safe := by sorry

def findRandom (gen : Gen α) (size : ℕ) (seed : ULift StdGen) (p : α -> Prop) [DecidablePred p] : Option α := do
  let res := ReaderT.run gen ⟨size⟩ |>.run seed
  if p res.1 then some res.1 else findRandom gen size res.2 p
  partial_fixpoint

instance {α : Type u} (p : α -> Prop) [SampleableExt α] [DecidablePred p] : WeakFindable p where
  find :=
    match (ST.Ref.get IO.stdGenRef : BaseIO StdGen) |>.run () with
    | .ok stdGen _ =>
      findRandom (SampleableExt.interpSample α) 100 (ULift.up stdGen) p
    | .error e _ => none
  find_some_p := by
    intro x; split <;> try simp
    rename_i seed _ _; revert x
    generalize ULift.up.{u, 0} seed = seed'; revert seed'
    apply findRandom.partial_correctness; simp
    introv ih; split_ifs; simp; rintro rfl; solve_by_elim
    solve_by_elim
