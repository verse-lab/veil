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

def random_transition (s : σ) : Gen (DivM (Except ExId (RelationalTransitionSystem.Transition σ labType))) := do
  let l <- genL
  return match nextComp l r₀ s with
    | .res (.ok ⟨_, s'⟩) => .res (.ok ⟨s', l⟩)
    | .res (.error e) => .res (.error e)
    | .div => .div

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
  expose_names; constructor
  { apply RelationalTransitionSystem.reachable.step _ _ h; exists x
    apply next_refine; simp [VeilExecM.operational, *] }
  apply next_refine; simp [VeilExecM.operational, *]

@[aesop safe cases]
structure RandomTrace (ρ σ labType) where
  trace : RelationalTransitionSystem.Trace ρ σ labType
  thrownException? : Option ExId
  numberOfSteps : Nat
  safe? : Bool

@[simp]
def RandomTrace.getLast (trace : RandomTrace ρ σ labType) : σ := trace.trace.getLast
def RandomTrace.push (trace : RandomTrace ρ σ labType) (s : σ) (l : labType) : RandomTrace ρ σ labType :=
  { trace with trace := trace.trace.push s l }

omit next_refine in
@[spec]
lemma Gen.runProp_triple (p : Prop) (cfg : Configuration) [Testable p] :
  triple ⊤ (Testable.runProp p cfg b) (fun
    | .success _ | .gaveUp _ => ⊤
    | .failure _ _ _ => ⌜¬ p⌝) := by
  apply triple_cons _ (le_refl _) _ (Gen.wp_rand _)
  rintro (_|_|_) <;> simp [*]

-- uncomment to use aesop
-- attribute [local simp] RelationalTransitionSystem.next
-- set_option maxHeartbeats 1000000
-- local add_aesop_rules safe RelationalTransitionSystem.Trace.push_isValid
-- local add_aesop_rules safe cases [DivM, Except]
-- local add_aesop_rules unsafe 50% apply [RelationalTransitionSystem.reachable.init]

def check_safety (steps : Nat) (cfg : Configuration) [∀ r s, Testable (sys.safe r s)] : Gen (RandomTrace ρ σ labType) := do
  let mut trace : RandomTrace ρ σ labType := ⟨⟨r₀, s₀, #[]⟩, .none, 0, true⟩
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

lemma check_safety_triple (steps : Nat) (cfg : Configuration) [∀ r s, Testable (sys.safe r s)] :
  triple
  ⌜sys.assumptions r₀ ∧ sys.init r₀ s₀⌝
    (check_safety genL nextComp r₀ s₀ steps cfg)
  (fun res => ⌜res.trace.isValid ∧ (sys.isInvariant sys.safe -> res.safe? = true)⌝) := by
  dsimp [check_safety]
  mwp; dsimp [check_safety.match_2.splitter, check_safety.match_1.splitter]
  -- this is aesop output:
  intro a a_1
  simp_all only [not_false_eq_true, ULift.forall, true_and]
  apply And.intro
  · intro b a_2 a_3 a_4 a_5 a_6 x x_1 x_2 a_7
    subst a_2 a_3
    cases x with
    | res x_3 =>
      simp_all only
      cases x_3 with
      | error a_2 => simp_all only [implies_true, and_self]
      | ok a_3 =>
        simp_all only
        intro x x_3 x_4 a_2
        obtain ⟨left, right⟩ := a_7
        obtain ⟨trace, thrownException?, numberOfSteps, safe?⟩ := b
        simp_all only
        split at a_2
        next x
          a_7 =>
          simp_all only [RelationalTransitionSystem.Trace.getLast_push, implies_true, and_self, and_true]
          cases a_7 with
          | inl val =>
            apply And.intro
            · rfl
            · apply And.intro
              · rfl
              · apply RelationalTransitionSystem.Trace.push_isValid
                · simp_all only
                · simp_all only
                · simp_all only
          | inr val_1 =>
            apply And.intro
            · rfl
            · apply And.intro
              · rfl
              · apply RelationalTransitionSystem.Trace.push_isValid
                · simp_all only
                · simp_all only
                · simp_all only
        next x
          a_7 =>
          simp_all only [RelationalTransitionSystem.Trace.getLast_push, implies_true, and_self, and_true]
          apply And.intro
          · rfl
          · apply And.intro
            · rfl
            · apply RelationalTransitionSystem.Trace.push_isValid
              · simp_all only
              · simp_all only
              · simp_all only
        next x a_7 a_8
          a_9 =>
          simp_all only [RelationalTransitionSystem.Trace.getLast_push, Bool.false_eq_true, implies_true, and_self,
            and_true]
          apply And.intro
          · rfl
          · apply And.intro
            · rfl
            · apply RelationalTransitionSystem.Trace.push_isValid
              · simp_all only
              · simp_all only
              · simp_all only
    | div => simp_all only [implies_true, and_self]
  · apply And.intro
    · apply And.intro
      · apply RelationalTransitionSystem.Trace.isValid_empty
        intro a_2
        simp_all only
      · apply RelationalTransitionSystem.reachable.init
        · simp_all only
        · simp_all only
    · intro x a_2 a_3 a_4 a_5 a_6 a_7
      subst a_3 a_2
      obtain ⟨trace, thrownException?, numberOfSteps, safe?⟩ := x
      simp_all only
      apply a_6
      apply a_7
      simp_all only


def findRandom (gen : Gen α) (size : ℕ) (seed : ULift StdGen) (p : α -> Prop) [DecidablePred p] : Option α := do
  let res := ReaderT.run gen ⟨size⟩ |>.run seed
  if p res.1 then some res.1 else findRandom gen size res.2 p
  partial_fixpoint

class VeilSampleSize (n : outParam Nat)

instance (priority := low) : VeilSampleSize 10 where

instance {α : Type u} (p : α -> Prop) [VeilSampleSize n] [SampleableExt α] [DecidablePred p] : WeakFindable p where
  find :=
    match (ST.Ref.get IO.stdGenRef : BaseIO StdGen) |>.run () with
    | .ok stdGen _ =>
      findRandom (SampleableExt.interpSample α) n (ULift.up stdGen) p
    | .error e _ => none
  find_some_p := by
    intro x; split <;> try simp
    rename_i seed _ _; revert x
    generalize ULift.up.{u, 0} seed = seed'; revert seed'
    apply findRandom.partial_correctness; simp
    introv ih; split_ifs; simp; rintro rfl; solve_by_elim
    solve_by_elim

instance Fin.shrinkable {n : Nat} : Shrinkable (Fin n) where
  shrink m :=
    match n with
    | 0 => []
    | _ + 1 => Nat.shrink m |>.map (Fin.ofNat' _)

instance Fin.sampleableExt {n : Nat} [inh : Inhabited (Fin n)] : SampleableExt (Fin n) where
  proxy := Fin n
  sample :=
    match n, inh with
    | 0, _ => return default
    | n + 1, _ => SampleableExt.sample (α := Fin (n+1))
  interp := id

instance [Inhabited α] [FinEnum α] : Inhabited (Fin (FinEnum.card α)) where
  default := FinEnum.equiv default

instance [Inhabited α] [FinEnum α] : SampleableExt α where
  proxy := Fin (FinEnum.card α)
  sample := SampleableExt.sample (α := Fin (FinEnum.card α))
  interp := FinEnum.equiv.symm

instance SampleableConstFun [SampleableExt α] [Repr α] [Shrinkable α] : SampleableExt (β → α) where
  proxy := α
  sample := SampleableExt.interpSample (α := α)
  interp a := fun _ => a

instance SampleableFun {β α : Type} [BEq β] [Inhabited α] [SampleableExt α] [Repr α] [Shrinkable α]
  [SampleableExt β] [Repr β] [Shrinkable β] :
  SampleableExt (β → α) where
  proxy := List (β × α)
  sample := SampleableExt.interpSample (α := List (β × α))
  interp l := fun b =>
    if let some ⟨_, a⟩ := l.find? (·.1 == b) then a else default

instance [FinEnum α] : Shrinkable α := inferInstanceAs (Shrinkable (NoShrink α))
instance [FinEnum α] : Repr α where reprPrec a n := reprPrec (FinEnum.equiv a) n
