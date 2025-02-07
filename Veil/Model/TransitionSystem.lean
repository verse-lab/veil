
-- NOTE: if you change this, make sure you also change
-- `findStateType` in `Tactic/Util.lean`
class RelationalTransitionSystem (σ : Type) where
  init : σ → Prop
  assumptions : σ → Prop
  next : σ -> σ -> Prop
  safe : σ → Prop
  inv : σ → Prop

namespace RelationalTransitionSystem
open RelationalTransitionSystem

/-- All states in the invariant are safe. -/
def invSafe [RelationalTransitionSystem σ] :=
  ∀ (s : σ), assumptions s -> inv s -> safe s

/-- The set of initial states are in the invariant. -/
def invInit [RelationalTransitionSystem σ] :=
  ∀ (s : σ), assumptions s -> init s -> inv s

/-- The invariant is preserved by transition. -/
def invConsecution [RelationalTransitionSystem σ] :=
  ∀ (s1 s2 : σ), assumptions s1 -> inv s1 -> next s1 s2 -> inv s2

/-- The invariant is inductive. -/
def invInductive [sys: RelationalTransitionSystem σ] :=
  @invInit σ sys ∧ @invConsecution σ sys

/-- `invInductive` with the property not necessarily being `inv`. -/
def isInductiveInvariant [sys: RelationalTransitionSystem σ] (p : σ → Prop) :=
  (∀ (s : σ), assumptions s → init s → p s) ∧
  (∀ (s s' : σ), assumptions s → p s → next s s' → p s')

inductive reachable [sys : RelationalTransitionSystem σ] : σ → Prop where
  | init : ∀ (s : σ), sys.init s → reachable s
  | step : ∀ (s s' : σ), reachable s → sys.next s s' → reachable s'

theorem reachable_inclusion (sys sys' : RelationalTransitionSystem σ)
  (hinit_implies : ∀ (st : σ), sys.init st → sys'.init st)
  (hnext_implies : ∀ (st st' : σ), sys.next st st' → sys'.next st st') :
  ∀ (st : σ), reachable (sys := sys) st → reachable (sys := sys') st := by
  intro st h
  induction h with
  | init s hinit => apply reachable.init ; apply hinit_implies ; assumption
  | step s s' h2 hn ih => apply reachable.step ; apply ih ; apply hnext_implies ; assumption

-- another characterization of invariant
def isInvariant [sys : RelationalTransitionSystem σ] (p : σ → Prop) : Prop := ∀ (s : σ), reachable s → p s

-- theorem invariant_split [sys : RelationalTransitionSystem σ] (p q : σ → Prop) :
--   (isInvariant (fun s => p s ∧ q s)) = (isInvariant p ∧ isInvariant q) := by
--   ext ; unfold isInvariant ; simp ; constructor
--   next => intro h ; constructor <;> intro s hh <;> specialize h s hh <;> cases h <;> assumption
--   next => intro ⟨ha, hb⟩ s hh ; specialize ha _ hh ; specialize hb _ hh ; constructor <;> assumption

theorem invariant_merge [sys : RelationalTransitionSystem σ] (p q : σ → Prop) :
  (isInvariant p ∧ isInvariant q) ↔ (isInvariant (fun s => p s ∧ q s)) := by
  unfold isInvariant ; simp ; constructor
  next => intro ⟨ha, hb⟩ s hh ; specialize ha _ hh ; specialize hb _ hh ; constructor <;> assumption
  next => intro h ; constructor <;> intro s hh <;> specialize h s hh <;> cases h <;> assumption

theorem isInductiveInvariant_to_isInvariant [sys : RelationalTransitionSystem σ] (hassu : isInvariant sys.assumptions) (p : σ → Prop) :
  isInductiveInvariant (sys := sys) p → isInvariant (sys := sys) p := by
  intro ⟨ha, hb⟩ s h
  induction h with
  | init s hinit => specialize hassu _ (.init _ hinit) ; apply ha <;> assumption
  | step s s' h2 hn ih => specialize hassu _ h2 ; apply hb <;> assumption

theorem invInductive_to_isInvariant [sys : RelationalTransitionSystem σ] (hassu : isInvariant sys.assumptions) :
  invInductive (sys := sys) → isInvariant (sys := sys) sys.inv := isInductiveInvariant_to_isInvariant hassu sys.inv

end RelationalTransitionSystem
