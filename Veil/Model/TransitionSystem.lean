
class RelationalTransitionSystem (ρ : Type) (σ : Type) where
  init : ρ → σ → Prop
  assumptions : ρ → σ → Prop
  next : ρ → σ -> σ -> Prop
  safe : ρ → σ → Prop
  inv : ρ → σ → Prop

namespace RelationalTransitionSystem
open RelationalTransitionSystem

/-- All states in the invariant are safe. -/
def invSafe [RelationalTransitionSystem ρ σ] :=
  ∀ (r : ρ) (s : σ), assumptions r s -> inv r s -> safe r s

/-- The set of initial states are in the invariant. -/
def invInit [RelationalTransitionSystem ρ σ] :=
  ∀ (r : ρ) (s : σ), assumptions r s -> init r s -> inv r s

/-- The invariant is preserved by transition. -/
def invConsecution [RelationalTransitionSystem ρ σ] :=
  ∀ (r : ρ) (s1 s2 : σ), assumptions r s1 -> inv r s1 -> next r s1 s2 -> inv r s2

/-- The invariant is inductive. -/
def invInductive [sys: RelationalTransitionSystem ρ σ] :=
  @invInit ρ σ sys ∧ @invConsecution ρ σ sys

/-- `invInductive` with the property not necessarily being `inv`. -/
def isInductiveInvariant [sys: RelationalTransitionSystem ρ σ] (p : ρ → σ → Prop) :=
  (∀ (r : ρ) (s : σ), assumptions r s → init r s → p r s) ∧
  (∀ (r : ρ) (s s' : σ), assumptions r s → p r s → next r s s' → p r s')

inductive reachable [sys : RelationalTransitionSystem ρ σ] (r : ρ) : σ → Prop where
  | init : ∀ (s : σ), sys.init r s → reachable r s
  | step : ∀ (s s' : σ), reachable r s → sys.next r s s' → reachable r s'

theorem reachable_inclusion (sys sys' : RelationalTransitionSystem ρ σ)
  (hinit_implies : ∀ (r : ρ) (st : σ), sys.init r st → sys'.init r st)
  (hnext_implies : ∀ (r : ρ) (st st' : σ), sys.next r st st' → sys'.next r st st') :
  ∀ (r : ρ) (st : σ), reachable (sys := sys) r st → reachable (sys := sys') r st := by
  intro r st h
  induction h with
  | init s hinit => apply reachable.init ; apply hinit_implies ; assumption
  | step s s' h2 hn ih => apply reachable.step ; apply ih ; apply hnext_implies ; assumption

-- another characterization of invariant
def isInvariant [sys : RelationalTransitionSystem ρ σ] (p : ρ → σ → Prop) : Prop := ∀ (r : ρ) (s : σ), reachable r s → p r s

-- theorem invariant_split [sys : RelationalTransitionSystem σ] (p q : σ → Prop) :
--   (isInvariant (fun s => p s ∧ q s)) = (isInvariant p ∧ isInvariant q) := by
--   ext ; unfold isInvariant ; simp ; constructor
--   next => intro h ; constructor <;> intro s hh <;> specialize h s hh <;> cases h <;> assumption
--   next => intro ⟨ha, hb⟩ s hh ; specialize ha _ hh ; specialize hb _ hh ; constructor <;> assumption

theorem invariant_merge [sys : RelationalTransitionSystem ρ σ] (p q : ρ → σ → Prop) :
  (isInvariant p ∧ isInvariant q) ↔ (isInvariant (fun r s => p r s ∧ q r s)) := by
  unfold isInvariant ; simp ; constructor
  next => intro ⟨ha, hb⟩ r s hh ; specialize ha _ _ hh ; specialize hb _ _ hh ; constructor <;> assumption
  next => intro h ; constructor <;> intro r s hh <;> specialize h _ _ hh <;> cases h <;> assumption

theorem isInductiveInvariant_to_isInvariant [sys : RelationalTransitionSystem ρ σ] (hassu : isInvariant sys.assumptions) (p : ρ → σ → Prop) :
  isInductiveInvariant (sys := sys) p → isInvariant (sys := sys) p := by
  intro ⟨ha, hb⟩ r s h
  induction h with
  | init s hinit => specialize hassu _ _ (.init _ hinit) ; apply ha <;> assumption
  | step s s' h2 hn ih => specialize hassu _ _ h2 ; apply hb <;> assumption

theorem invInductive_to_isInvariant [sys : RelationalTransitionSystem ρ σ] (hassu : isInvariant sys.assumptions) :
  invInductive (sys := sys) → isInvariant (sys := sys) sys.inv := isInductiveInvariant_to_isInvariant hassu sys.inv

end RelationalTransitionSystem
