import Lean
import Lean.Parser
import Veil.Util.Meta
import Veil.Util.DSL
import Veil.Model.TransitionSystem
import Veil.DSL.Specification.SpecDef
import Veil.Theory.Basic
import Plausible

open Lean Lean.Elab.Command Lean.Meta Lean.Elab.Term

def deriveGen (instsForEachArg : Array Name) (inductiveTypeStx : Term) : TermElabM Syntax := do
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
  -- get the names of the parameters from the type, prepare instance premises
  let numParams := inductiveInfo.numParams
  let .some (paramNames, _) := Nat.foldM (m := Option) numParams (fun _ _ (res, ty) => do
    let Expr.forallE na _ body _ := ty | failure
    pure (na :: res, body)) ([], inductiveTypeConst.type) | throwError "unknown error"
  let paramIdents := paramNames.toArray |>.map mkIdent
  let paramInsts : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) ←
    paramIdents.flatMapM (fun pn => instsForEachArg.mapM fun a => `(bracketedBinder| [$(mkIdent a) $pn] ))
  -- work on each constructor
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
      sampleArg := sampleArg.push $ <- `(term| (← Plausible.SampleableExt.interpSample _))
    sampleArgs := sampleArgs.push $ sampleArg
  let target := Syntax.mkApp (mkIdent inductiveType) paramIdents
  let cmd ← `(command| def $(mkIdent $ inductiveType ++ `gen) $[$paramInsts]* :
     Plausible.Gen ($target) := do
        match ← Plausible.Gen.chooseAny (Fin $(Syntax.mkNatLit ctorsNum):term) with
        $[| Fin.mk $nums _ => return $ctorNames $sampleArgs* ]*)
  trace[veil.debug] "[deriveGen] {cmd}"
  pure cmd

/-- Derive a random generator for the specified inductive type. -/
elab "#deriveGen" t:term : command => do
  let stx <- runTermElabM (fun _ => deriveGen #[``Plausible.SampleableExt] t)
  elabCommand stx

/-- Similar to `#deriveGen`, but this requires more typeclass instance
    arguments, so that more complicated instances of `Plausible.SampleableExt`
    might get automatically synthesized for each constructor of the inductive type. -/
elab "#deriveGen! " t:term : command => do
  let stx ← runTermElabM (fun _ => deriveGen #[``Plausible.SampleableExt, ``Repr, ``DecidableEq] t)
  elabCommand stx

open Plausible

variable {labType : Type} [sys : RelationalTransitionSystem ρ σ labType]
variable  (genL : Gen labType)
variable (nextComp : labType -> VeilExecM .external ρ σ Unit)
variable (next_refine : ∀ (l : labType) (rd : ρ) (st st' : σ),
  (nextComp l).operational rd st st' (Except.ok ()) ->
  sys.nextLab rd st l st')
variable (r₀ : ρ) (s₀ : σ)

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
deriving Inhabited, Repr, BEq

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

open RelationalTransitionSystem in
def runAsInstructedStep (l : labType) : StateT σ (ExceptT ExId DivM) (Transition σ labType) := do
  let spre ← get
    let res := (nextComp l) |>.run r₀ |>.run spre
    match res with
    | .res (.ok ⟨_, s'⟩) => do
      set s'
      pure <| ⟨s', l⟩
    | .res (.error e) => throw e
    | .div => .div

-- NOTE: this thing __DOES NOT__ yet check the safety invariant!! it just runs the
-- actions as instructed by the labels in `ls`, and returns the trace
-- also, though it seems to handle exceptions, it does report them in the final result
open RelationalTransitionSystem in
def runAsInstructed (ls : Array labType) : Option (RandomTrace ρ σ labType) :=
  let tmp := ls.mapM (runAsInstructedStep nextComp r₀) |>.run s₀
  match tmp with
  | .res (.ok (res, _)) => .some <| RandomTrace.mk (Trace.mk r₀ s₀ res) none res.size false
  | _ => none

include next_refine in
open RelationalTransitionSystem in
theorem runAsInstructed_correct (ls : Array labType) res :
  runAsInstructed nextComp r₀ s₀ ls = some res →
  res.trace.tr.isValidFrom res.trace.r₀ res.trace.s₀ ∧ res.trace.tr.size = ls.size := by
  intro h
  dsimp [runAsInstructed] at h ; split at h <;> try contradiction
  injection h ; subst res ; dsimp ; rename_i res tmp heq
  -- use `List` instead of `Array` to prove things
  rw [Array.mapM_eq_mapM_toList] at heq ; rewrite (occs := .pos [2]) [Array.size_eq_length_toList]
  generalize ls.toList = ls' at * ; clear ls ; rename' ls' => ls
  revert s₀ res heq ; induction ls with
  | nil =>
    intro s₀ res heq ; simp at heq ; simp [pure, ExceptT.pure, ExceptT.mk] at heq
    injection heq ; rename_i heq ; injection heq ; rename_i heq ; simp at heq ; rcases heq with ⟨a, b⟩ ; subst_vars
    simp [StateTrace.isValidFrom]
  | cons l ls ih =>
    intro s₀ res heq
    -- destruct first, so to make it easier to use `ih`
    rw [List.mapM_cons] at heq ; simp only [bind_pure_comp, map_bind, Functor.map_map,
      StateT.run_bind, StateT.run_map] at heq
    rcases h1 : (runAsInstructedStep nextComp r₀ l).run s₀ with ( ( _ | ⟨ts, spost⟩ ) | _ )
    all_goals (rw [h1] at heq ; dsimp [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont.eq_1, ExceptT.bindCont.eq_2, pure] at heq ; try contradiction)
    on_goal 1=> injection heq ; contradiction
    rcases h2 : (List.mapM (runAsInstructedStep nextComp r₀) ls).run spost with ( ( _ | ⟨respre, _⟩ ) | _ )
    all_goals (rw [h2] at heq ; dsimp [Functor.map, ExceptT.map, ExceptT.mk, bind, pure] at heq ; try contradiction)
    on_goal 1=> injection heq ; contradiction
    injection heq ; rename_i heq ; injection heq ; rename_i heq ; simp at heq ; rcases heq with ⟨a, b⟩ ; subst_vars
    specialize ih spost respre.toArray
    simp only [StateT.run_map, List.size_toArray] at ih ; rw [h2] at ih ; specialize ih rfl
    rcases ih with ⟨ih1, ih2⟩ ; simp [ih2]
    unfold StateTrace.isValidFrom
    -- now reason about `ts` and `spost`
    simp [runAsInstructedStep, ReaderT.run] at h1
    rcases h : (nextComp l r₀).run s₀ with ( ( _ | ⟨_, spost⟩ ) | _ )
    all_goals (rw [h] at h1 ; dsimp at h1 ; try contradiction)
    on_goal 1=>
      dsimp only [throw, throwThe, MonadExceptOf.throw, Function.comp] at h1
      simp only [StateT.run_lift, ExceptT.mk] at h1
      dsimp only [pure, ExceptT.pure, ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont.eq_2] at h1
      injection h1 ; contradiction
    simp at h1 ; simp [pure, ExceptT.pure, ExceptT.mk] at h1
    injection h1 ; rename_i h1 ; injection h1 ; rename_i h1 ; simp at h1 ; rcases h1 with ⟨a, b⟩ ; subst_vars
    simp [ih1] ; apply next_refine ; unfold VeilExecM.operational ; dsimp [StateT.run] at h ; rw [h] ; simp

def findRandom (gen : Gen α) (size : ℕ) (seed : ULift StdGen) (p : α -> Prop) [DecidablePred p] : Option α := do
  let res := ReaderT.run gen ⟨size⟩ |>.run seed
  if p res.1 then some res.1 else findRandom gen size res.2 p
  partial_fixpoint

def findRandomFinEnum [FinEnum α] (gen : ∀ n [Inhabited (Fin n)], Gen (Fin n)) (size : ℕ) (seed : ULift StdGen) (p : α → Prop) [DecidablePred p] : Option α := do
  let l := FinEnum.toList α |>.filter p
  if h : l.isEmpty then none else
    let res := ReaderT.run (@gen l.length ⟨0, List.length_pos_iff.mpr <| List.isEmpty_eq_false_iff.mp <| eq_false_of_ne_true h⟩) ⟨size⟩ |>.run seed
    .some <| l.get res.1

class VeilSampleSize (n : outParam Nat)

instance (priority := low) : VeilSampleSize 10 where

/-
instance {α : Type} (p : α -> Prop) [VeilSampleSize n] [SampleableExt α] [DecidablePred p] : WeakFindable p where
  find :=
    let x := ((do
      let stdGen <- ST.Ref.get IO.stdGenRef
      dbg_trace "{stdGen.s1} {stdGen.s2}"
      if let some ⟨a, ⟨stdGen⟩⟩ := findRandom (SampleableExt.interpSample α) n (ULift.up stdGen) p then
        let _ <- ST.Ref.set IO.stdGenRef stdGen
        dbg_trace "{stdGen.s1} {stdGen.s2}"
        return some a
      else return none) : BaseIO (Option α)).run ()
    match x with
    | .ok a _ => a
    | .error e _ => none
  find_some_p := by sorry
-/
def findCore {α : Type} [VeilSampleSize n] (oracle : Nat → ULift.{u_1, 0} StdGen → Option α) : Option α :=
  let x := ((do
    let stdGen := mkStdGen (<- IO.rand 0 100)
    if let some a := oracle n (ULift.up stdGen) then
      return some a
    else return none) : BaseIO (Option α)).run ()
  match x with
  | .ok a _ => a
  | .error _ _ => none

instance Fin.shrinkable {n : Nat} : Shrinkable (Fin n) where
  shrink m :=
    match n with
    | 0 => []
    | _ + 1 => Nat.shrink m |>.map (Fin.ofNat' _)

instance [inh : Inhabited (Fin n)] : NeZero n := ⟨
  by cases n; simp; rcases inh with ⟨⟨_, f⟩⟩; simp at f; simp
⟩

instance (priority := high) Fin.sampleableExt {n : Nat} [inh : Inhabited (Fin n)] : SampleableExt (Fin n) where
  proxy := Fin n
  sample := do
    let x <- Plausible.Gen.choose Nat 0 (n - 1) (Nat.zero_le _)
    -- dbg_trace "y: {x} {n - 1}"
    return Fin.ofNat' n x
  interp := id

instance {α : Type} (p : α -> Prop) [VeilSampleSize n] [SampleableExt α] [DecidablePred p] : WeakFindable p where
  find u := findCore (fun a b => findRandom (SampleableExt.interpSample α) a b p)
  find_some_p := by
    intro x; simp [findCore, EStateM.run, bind, EStateM.bind, dbgTrace]; split <;>
    rename_i heq <;> revert heq <;> split <;> try simp
    -- rename_i heq; revert heq; split; try simp
    rename_i seed _ _
    cases h: (findRandom (SampleableExt.interpSample α) n { down := _ } p) <;> try simp [pure, EStateM.pure]
    { aesop }
    rename_i val; revert val h
    generalize ULift.up.{0, 0} (mkStdGen _) = seed';
    revert seed';
    apply findRandom.partial_correctness
    all_goals aesop

instance (priority := high) Findable.byFinEnum {α : Type} [FinEnum α] (p : α -> Prop) [VeilSampleSize n] [SampleableExt α] [DecidablePred p] : Findable p where
  find u := findCore (fun a b => findRandomFinEnum (fun n => SampleableExt.interpSample (Fin n)) a b p)
  find_some_p := by
    intro x; simp [findCore, EStateM.run, bind, EStateM.bind] ; intro h ; split at h <;> (try contradiction)
    rename_i heq ; split at heq <;> (try contradiction)
    rename_i seed _ _
    cases h : (findRandomFinEnum (fun n [Inhabited (Fin n)] => SampleableExt.interpSample (Fin n)) n { down := mkStdGen seed } p) <;> rw [h] at heq <;> simp [pure, EStateM.pure] at heq <;> rcases heq with ⟨_, _⟩ <;> subst_vars
    { contradiction }
    rename_i val hh ; simp at hh ; subst_vars ; simp [findRandomFinEnum] at h
    rcases h with ⟨_, h⟩
    have htmp := @List.mem_filter _ (fun b => decide (p b)) (FinEnum.toList α) val
    subst_vars ; simp at htmp ; exact htmp
  find_none := by
    intro h x ; simp [findCore, EStateM.run, bind, EStateM.bind] at h ; split at h <;> (try contradiction)
    rename_i heq ; split at heq <;> (try contradiction)
    rename_i seed _ _
    cases h : (findRandomFinEnum (fun n [Inhabited (Fin n)] => SampleableExt.interpSample (Fin n)) n { down := mkStdGen seed } p) <;> rw [h] at heq <;> simp [pure, EStateM.pure] at heq <;> rcases heq with ⟨_, _⟩ <;> subst_vars
    on_goal 2=> contradiction
    simp [findRandomFinEnum] at h ; apply h

instance (priority := high) WeakFindable.byFinEnum {α : Type} [FinEnum α] (p : α -> Prop) [VeilSampleSize n] [SampleableExt α] [DecidablePred p] : WeakFindable p :=
  @WeakFindable.of_Findable _ _ (Findable.byFinEnum p)

instance (priority := high) Fin.sampleableExtBool : SampleableExt Bool where
  proxy := Nat
  sample := do Gen.choose Nat 0 (<- Gen.getSize) (Nat.zero_le _)
  interp := (· % 2 = 1)

instance [Inhabited α] [FinEnum α] : Inhabited (Fin (FinEnum.card α)) where
  default := FinEnum.equiv default

instance [Inhabited α] [FinEnum α] : SampleableExt α where
  proxy := Fin (FinEnum.card α)
  sample := SampleableExt.sample (α := Fin (FinEnum.card α))
  interp := FinEnum.equiv.symm

instance (priority := low) SampleableConstFun [SampleableExt α] [Repr α] [Shrinkable α] : SampleableExt (β → α) where
  proxy := α
  sample := SampleableExt.interpSample (α := α)
  interp a := fun _ => a

/-
-- temporarily commented out, due to the existing `Plausible.TotalFunction.Pi.sampleableExt` instance
instance SampleableFun {β α : Type} [BEq β] [Inhabited α] [SampleableExt α] [Repr α] [Shrinkable α]
  [SampleableExt β] [Repr β] [Shrinkable β] :
  SampleableExt (β → α) where
  proxy := List (β × α)
  sample := SampleableExt.interpSample (α := List (β × α))
  interp l := fun b =>
    if let some ⟨_, a⟩ := l.find? (·.1 == b) then a else default
-/

instance [FinEnum α] : Shrinkable α := inferInstanceAs (Shrinkable (NoShrink α))
instance [FinEnum α] : Repr α where reprPrec a n := reprPrec (FinEnum.equiv a) n
