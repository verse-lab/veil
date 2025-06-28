import Aesop

class RelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) where
  /-- The set of acceptable background theories -/
  assumptions : ρ → Prop
  /-- The set of initial states, indexed by background theory they
  operate in -/
  init : ρ → σ → Prop
  /-- The transition relation -/
  nextLab : ρ → σ → l → σ → Prop
  safe : ρ → σ → Prop
  inv : ρ → σ → Prop

  initSatisfiesAssumptions : ∀ (r : ρ) (s : σ), init r s → assumptions r

def RelationalTransitionSystem.next [RelationalTransitionSystem ρ σ l] (r : ρ) (s : σ) (s' : σ) : Prop :=
  ∃ l, nextLab r s l s'

namespace RelationalTransitionSystem
open RelationalTransitionSystem


/-- All states in the invariant are safe. -/
def invSafe [RelationalTransitionSystem ρ σ l] :=
  ∀ (r : ρ) (s : σ), @assumptions ρ σ l _ r -> inv r s -> safe r s

/-- The set of initial states are in the invariant. -/
def invInit [RelationalTransitionSystem ρ σ l] (p : ρ → σ → Prop) :=
  ∀ (r : ρ) (s : σ), @assumptions ρ σ l _ r -> init r s -> p r s

/-- The invariant is preserved by transition. -/
def invConsecution [RelationalTransitionSystem ρ σ l] (p : ρ → σ → Prop) :=
  ∀ (r : ρ) (s1 s2 : σ), @assumptions ρ σ l _ r -> p r s1 -> next r s1 s2 -> p r s2

/-- The invariant is inductive. -/
def isInductive [sys: RelationalTransitionSystem ρ σ l] (p : ρ → σ → Prop) :=
  @invInit ρ σ l sys p ∧ @invConsecution ρ σ l sys p

/-- Reachability relation, indexed by background theory -/
@[aesop safe constructors]
inductive reachable [sys : RelationalTransitionSystem ρ σ l] (r : ρ) : σ → Prop where
  | init : ∀ (s : σ), sys.assumptions r → sys.init r s → reachable r s
  | step : ∀ (s s' : σ), reachable r s → sys.next r s s' → reachable r s'

/-- Assumptions hold in all reachable states. -/
theorem reachable_assumptions [sys : RelationalTransitionSystem ρ σ l] (r : ρ) (s : σ) (h : reachable r s) : sys.assumptions r := by
  induction h with
  | init s has hinit => assumption
  | step s s' h2 hn ih => assumption

theorem reachable_inclusion (sys sys' : RelationalTransitionSystem ρ σ l)
  (hass_implies : ∀ (r : ρ), sys.assumptions r → sys'.assumptions r)
  (hinit_implies : ∀ (r : ρ) (st : σ), sys.init r st → sys'.init r st)
  (hnext_implies : ∀ (r : ρ) (st st' : σ), sys.next r st st' → sys'.next r st st') :
  ∀ (r : ρ) (st : σ), reachable (sys := sys) r st → reachable (sys := sys') r st := by
  intro r st h
  induction h with
  | init s has hinit => apply reachable.init _ (hass_implies r has) (hinit_implies r s hinit)
  | step s s' h2 hn ih => apply reachable.step ; apply ih ; apply hnext_implies ; assumption

/-- The property holds in all reachable states. -/
def isInvariant [sys : RelationalTransitionSystem ρ σ l] (p : ρ → σ → Prop) : Prop := ∀ (r : ρ) (s : σ), reachable r s → p r s

theorem invariant_merge [sys : RelationalTransitionSystem ρ σ l] (p q : ρ → σ → Prop) :
  (isInvariant p ∧ isInvariant q) ↔ (isInvariant (fun r s => p r s ∧ q r s)) := by
  unfold isInvariant ; simp ; constructor
  next => intro ⟨ha, hb⟩ r s hh ; specialize ha _ _ hh ; specialize hb _ _ hh ; constructor <;> assumption
  next => intro h ; constructor <;> intro r s hh <;> specialize h _ _ hh <;> cases h <;> assumption

theorem inductive_is_invariant [sys : RelationalTransitionSystem ρ σ l] (p : ρ → σ → Prop) :
  isInductive (sys := sys) p → isInvariant (sys := sys) p := by
  intro ⟨ha, hb⟩ r s₀ h
  induction h with
  | init s hass hinit => apply (ha _ _ hass hinit)
  | step s s' h2 hn ih => apply (hb r _ _ (reachable_assumptions r s h2) ih hn)

theorem isInvariant_reachable [sys : RelationalTransitionSystem ρ σ l] (p : ρ → σ → Prop) :
  isInvariant (sys := sys) p → ∀ (r : ρ) (s : σ), reachable r s → p r s := by
  intro h r s hh
  induction hh with
  | init s hass hinit => aesop (add safe apply reachable.init)
  | step s s' h2 hn ih => aesop (add safe apply reachable.step)

structure Transition (σ l : Type) where
  postState : σ
  label : l

abbrev StateTrace (σ l : Type) := Array (Transition σ l)

structure Trace (ρ σ l : Type) where
  r₀ : ρ
  s₀ : σ
  tr : StateTrace σ l

def StateTrace.isValidFrom [sys : RelationalTransitionSystem ρ σ l] (r : ρ) (s : σ) (ts : StateTrace σ l) : Prop :=
  match _ : ts.toList with
  | [] => True
  | ⟨s', l⟩ :: ts' => sys.nextLab r s l s' ∧ isValidFrom r s' ts'.toArray
termination_by ts.size
decreasing_by
  rename_i h; simp
  have := congrArg List.length h
  simp at this; omega

def StateTrace.push (ts : StateTrace σ l) (s : σ) (la : l) : StateTrace σ l :=
  Array.push ts ⟨s, la⟩

def StateTrace.getLastD  (s : σ) (ts : StateTrace σ l) : σ :=
  if let some ⟨s', _⟩ := ts.back? then s' else s

def Trace.getLast (t : Trace ρ σ l) : σ :=
  t.tr.getLastD t.s₀

def Trace.push (t : Trace ρ σ l) (s : σ) (la : l) : Trace ρ σ l :=
  { t with tr := t.tr.push s la }

@[simp]
theorem StateTrace.getLastD_push (s : σ) (ts : StateTrace σ l) (s' : σ) (la : l) :
  (ts.push s' la).getLastD s = s' := by
  simp [getLastD, push]

@[simp]
theorem Trace.getLast_push (t : Trace ρ σ l) (s : σ) (la : l) :
  (t.push s la).getLast = s := by
  simp [getLast, push]

theorem StateTrace.push_isValidFrom [sys : RelationalTransitionSystem ρ σ l]
  (r : ρ) (s : σ) (ts : StateTrace σ l) (s' : σ) (la : l) :
  ts.isValidFrom r s ->
  sys.nextLab r (ts.getLastD s) la s' ->
  (ts.push s' la).isValidFrom r s := by
  unhygienic fun_induction StateTrace.isValidFrom generalizing la s'
  { cases ts_1 <;> simp at *
    simp [*]; unfold StateTrace.isValidFrom; unfold StateTrace.push;
    simp [Array.push, List.concat]
    unfold StateTrace.isValidFrom; simp [getLastD] }
  rename_i s
  unfold isValidFrom; rw [h]; simp
  unfold StateTrace.push; simp [Array.push]
  rw [h]; simp [List.concat]
  intro h' vl nx; constructor <;> try assumption
  have : (push ts'.toArray s' la) = (ts' ++ [Transition.mk s' la]).toArray := by
    rw [<-Array.toList_inj]
    simp [push]
  rw [<-this]; apply ih1; assumption
  have : ts_1 = ts_1.toList.toArray := by simp
  rw [this] at nx; revert nx
  simp [h, getLastD, List.getLast?_cons]
  cases ts'.getLast? <;> simp

def Trace.isValid [sys : RelationalTransitionSystem ρ σ l] (t : Trace ρ σ l) : Prop :=
  sys.assumptions t.r₀ -> t.tr.isValidFrom t.r₀ t.s₀

theorem Trace.push_isValid [sys : RelationalTransitionSystem ρ σ l] (t : Trace ρ σ l) (s : σ) (l : l) :
  t.isValid ->
  sys.nextLab t.r₀ t.getLast l s ->
  (t.push s l).isValid := by
  cases t <;> simp [getLast, isValid, push]
  intros; solve_by_elim [StateTrace.push_isValidFrom]



end RelationalTransitionSystem
