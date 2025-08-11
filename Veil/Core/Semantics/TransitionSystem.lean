
/-- A background theory is a set of structures (of type `ρ`) which
satisfy the `assumptions` made about them. -/
class BackgroundTheory (ρ : Type) where
  assumptions : ρ → Prop

/-- A relational transition system is parametrised by:
  - a background theory over immutable structures `ρ`,
  - a mutable state space `σ`, and
  - a label space `l`, which describe the transitions that can be
  taken, together with their arguments (if any).

  It describes the initial states (`init`) and transitions (`tr`) of
  the system as relations.
-/
class RelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) extends BackgroundTheory ρ where
  /-- The set of initial states, indexed by background theory they
  operate in -/
  init : ρ → σ → Prop
  /-- The transition relation -/
  tr : ρ → σ → l → σ → Prop

def RelationalTransitionSystem.next [RelationalTransitionSystem ρ σ l] (bg : ρ) (s : σ) (s' : σ) : Prop :=
  ∃ lab, tr bg s lab s'
