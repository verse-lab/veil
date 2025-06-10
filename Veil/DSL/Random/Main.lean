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

variable [sys : RelationalTransitionSystem ρ σ]
variable {labType : Type} (genL : Gen labType)
variable (nextComp : labType -> VeilExecM .external ρ σ Unit)
variable (next_refine : ∀ (rd : ρ) (st st' : σ) (l : labType),
  (nextComp l).operational rd st st' (Except.ok ()) ->
  sys.next rd st st')
variable (r₀ : ρ) (s₀ : σ) (hinit : sys.init r₀ s₀)

#check Random Id labType

def random_transition (s : σ) : Gen (DivM (Except ExId σ)) := do
  let l <- genL
  return match nextComp l |>.run r₀ s with
    | .res (.ok ⟨_, s'⟩) => .res (.ok s')
    | .res (.error e) => .res (.error e)
    | .div => .div

structure RandomTrace (σ : Type) where
  trace : Array σ
  thrownException? : Option ExId
  numberOfSteps : Nat
  safe? : Bool

def check_safety (steps : Nat) (cfg : Configuration) [∀ r s, Testable (sys.safe r s)] : Gen (RandomTrace σ) := do
  let mut trace := #[]
  let mut s := s₀
  let mut numberOfSteps := 0
  for _ in [0:steps] do
    let step ← random_transition genL nextComp r₀ s
    match step with
    | .res (.ok s') =>
      match <- Testable.runProp (sys.safe r₀ s') cfg true with
      | .success _ | .gaveUp _ =>
        s := s'
        trace := trace.push s
        numberOfSteps := numberOfSteps + 1
      | .failure _ _ _ =>
        return ⟨trace, .none, numberOfSteps, false⟩
    | .res (.error e) =>
      return ⟨trace, .some e, numberOfSteps, false⟩
    | .div => pure ()
  return ⟨trace, .none, numberOfSteps, true⟩

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
