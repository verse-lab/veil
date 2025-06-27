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

variable {labType : Type} [sys : RelationalTransitionSystem ρ σ labType]
variable  (genL : Gen labType)
variable (nextComp : labType -> VeilExecM .external ρ σ Unit)
variable (next_refine : ∀ (rd : ρ) (st st' : σ) (l : labType),
  (nextComp l).operational rd st st' (Except.ok ()) ->
  sys.nextLab rd st l st')
variable (r₀ : ρ) (s₀ : σ) (hinit : sys.init r₀ s₀)

def random_transition (s : σ) : Gen (DivM (Except ExId sys.Transition)) := do
  let l <- genL
  return match nextComp l |>.run r₀ s with
    | .res (.ok ⟨_, s'⟩) => .res (.ok ⟨s', l⟩)
    | .res (.error e) => .res (.error e)
    | .div => .div

-- attribute [spec low] Gen.wp_rand


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
@[spec]
lemma random_transition_spec (s : σ) :
  triple
    ⌜sys.reachable r₀ s⌝
    (random_transition genL nextComp r₀ s)
    (fun
      | .res (.ok tr) => ⌜sys.reachable r₀ tr.postState ∧ sys.nextLab r₀ s tr.label tr.postState⌝
      | _ => ⊤) := by
  simp [random_transition]
  mwp; apply WPGen.spec_triple; apply Gen.wp_rand
  simp [loomWpSimp, loomLogicSimp]
  intros; split <;> simp
  expose_names; simp [ReaderT.run] at heq
  constructor
  { apply RelationalTransitionSystem.reachable.step _ _ h; exists x
    apply next_refine; simp [VeilExecM.operational, *] }
  apply next_refine; simp [VeilExecM.operational, *]

@[aesop safe cases]
structure RandomTrace (ρ σ) [sys : RelationalTransitionSystem ρ σ labType] where
  trace : sys.Trace ρ σ
  thrownException? : Option ExId
  numberOfSteps : Nat
  safe? : Bool

@[simp]
def RandomTrace.getLast (trace : RandomTrace ρ σ) : σ := trace.trace.getLast
def RandomTrace.push (trace : RandomTrace ρ σ) (s : σ) (l : labType) : RandomTrace ρ σ :=
  { trace with trace := trace.trace.push s l }

def check_safety (steps : Nat) (cfg : Configuration) [∀ r s, Testable (sys.safe r s)] : Gen (RandomTrace ρ σ) := do
  let mut trace : RandomTrace ρ σ := ⟨⟨r₀, s₀, #[]⟩, .none, 0, true⟩
  for _st in [0:steps]
  invariant ⌜trace.trace.r₀ = r₀⌝
  invariant ⌜trace.trace.s₀ = s₀⌝
  invariant ⌜trace.trace.isValid⌝
  invariant ⌜sys.reachable r₀ trace.getLast⌝
  invariant ⌜sys.safe r₀ trace.getLast -> trace.safe? = true⌝
  do
    let step ← random_transition genL nextComp r₀ trace.getLast
    match step with
    | .res (.ok ⟨s', l⟩) =>
      match <- Testable.runProp (sys.safe r₀ s') cfg true with
      | .success _ | .gaveUp _ =>
        trace :=
          { trace with
            trace := trace.trace.push s' l,
            numberOfSteps := trace.numberOfSteps + 1
            safe? := true }
      | .failure _ _ _ =>
        trace :=
        { trace with
          trace := trace.trace.push s' l,
          numberOfSteps := trace.numberOfSteps + 1,
          safe? := false }
        break
    | .res (.error e) =>
      trace := { trace with thrownException? := e, safe? := true }
      break
    | .div => pure ()
  return trace

omit next_refine in
@[spec]
lemma Gen.runProp_triple (p : Prop) (cfg : Configuration) [Testable p] :
  triple ⊤ (Testable.runProp p cfg b) (fun
    | .success _ | .gaveUp _ => ⊤
    | .failure _ _ _ => ⌜¬ p⌝) := by
  apply triple_cons _ (le_refl _) _ (Gen.wp_rand _)
  rintro (_|_|_) <;> simp [*]

attribute [simp] RelationalTransitionSystem.next

set_option maxHeartbeats 1000000

add_aesop_rules safe RelationalTransitionSystem.Trace.push_isValid

lemma check_safety_triple (steps : Nat) (cfg : Configuration) [∀ r s, Testable (sys.safe r s)] :
  sys.isInvariant sys.safe ->
  triple ⌜sys.assumptions r₀ ∧ sys.init r₀ s₀⌝
  (check_safety genL nextComp r₀ s₀ steps cfg)
  (fun res => ⌜res.trace.isValid ∧ res.safe? = true⌝) := by
  intro sf; dsimp [check_safety]
  mwp
  intro ass ini; constructor
  { intro tr _ _ invVal invReach invSafe; constructor; assumption
    dsimp [check_safety.match_2.splitter, check_safety.match_1.splitter]
    rintro ((ex|_)|_) <;> aesop }
  constructor
  { simp [RelationalTransitionSystem.Trace.getLast,
    RelationalTransitionSystem.StateTrace.getLastD,
    RelationalTransitionSystem.Trace.isValid,
    RelationalTransitionSystem.StateTrace.isValidFrom]
    solve_by_elim }
  aesop


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
