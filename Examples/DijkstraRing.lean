import Veil
import Veil.DSL.Random.ExtractUtil
import Veil.DSL.Random.Extract
import Veil.DSL.Random.Main

class FiniteRing (t : Type) where
  -- relation: strict total order
  le (x y : t) : Prop
  -- axioms
  le_refl (x : t) : le x x
  le_trans (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total (x y : t) : le x y ∨ le y x

  -- relation: nonstrict total order
  lt (x y : t) : Prop
  le_lt (x y : t) : lt x y ↔ (le x y ∧ x ≠ y)

  bottom : t
  bottom_lt (x : t) : le bottom x

  top : t
  top_gt (x : t) : le x top

  bottom_neq_top : bottom ≠ top

  -- successor on the ring
  next (x y : t) : Prop
  next_def (x y : t) : next x y ↔ ((lt x y ∧ ∀ z, lt x z → le y z) ∨ (x = top ∧ y = bottom))

instance (n : Nat) : FiniteRing (Fin n.succ.succ) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega

  lt := fun x y => x.val < y.val
  le_lt := by simp ; omega

  bottom := Fin.mk 0 (Nat.lt_trans (Nat.zero_lt_succ n) (Nat.le_refl _))
  bottom_lt := by simp

  top := Fin.mk n.succ (Nat.le_refl _)
  top_gt := by rintro ⟨x, h⟩ ; exact Nat.le_of_lt_succ h

  bottom_neq_top := by simp

  next := fun x y =>
    if x.val < n.succ then y.val = x.val.succ else y.val = 0
  next_def := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ; simp only [Fin.mk.injEq] ; split_ifs
    next h =>
      constructor
      · intro ; subst y ; left ; refine And.intro (Nat.le_refl _) ?_
        rintro ⟨z, hz⟩ ; dsimp only [Fin.val] ; exact id
      · rintro ( ⟨h1, h2⟩ | ⟨h1, h2⟩ )
        · specialize h2 ⟨x.succ, Nat.succ_lt_succ h⟩ (Nat.le_refl _) ; dsimp only [Fin.val] at h2
          exact Nat.eq_of_le_of_lt_succ h1 (Nat.lt_succ_of_le h2)
        · subst x ; simp only [lt_self_iff_false] at h
    next h =>
      have a := Nat.eq_of_lt_succ_of_not_lt hx h ; subst x ; clear hx h
      constructor
      · intro ; subst y ; right ; constructor <;> rfl
      · rintro ( ⟨h1, h2⟩ | ⟨h1, h2⟩ )
        · have htmp := Nat.lt_of_le_of_lt h1 hy ; simp only [lt_self_iff_false] at htmp
        · assumption

veil module DijkstraRing

type node
instantiate ring : FiniteRing node

open FiniteRing

function x : node → Bool
function up : node → Bool

#gen_state

invariant [up_bottom] up (ring.bottom) = True
invariant [up_top] up (ring.top) = False


ghost relation hasPrivilege (s : node) :=
  ∀ (l r : node), next l s ∧ next s r →
    if s = ring.bottom then
      (x s = x r) ∧ (¬ up r)
    else if s = ring.top then
      x s ≠ x l
    else
      (x s ≠ x l) ∨ ((x s = x r) ∧ (up s) ∧ (¬ up r))

safety [at_least_one_privilege] ∃ n, hasPrivilege n

after_init {
  up (ring.bottom) := true
  up (ring.top) := false
}

action step (s : node) = {
  let (l, r) :| next l s ∧ next s r
  if s = ring.bottom then
    if x s = x r ∧ (¬ up r) then
      x s := ¬ x s
  else
    if s = ring.top then
      if x s ≠ x l then
          x s := ¬ x s
    else
      if x s ≠ x l then
        x s := not <| x s
        up s := true
      if x s = x r ∧ up s ∧ (¬ up r) then
        up s := false
}

#gen_spec
/-
#check_invariants

set_option veil.smt.translator "lean-smt"
set_option veil.smt.solver "cvc5"
set_option maxHeartbeats 10000000

sat trace [initial_state_exists] { } by bmc_sat

unsat trace [cannot_revert_to_more_than_one_privilege] {
  assert (∃ (a : node), hasPrivilege a ∧ (∀ (b : node), a ≠ b → ¬ hasPrivilege b))
  any 10 actions
  assert (∃ (a b : node), a ≠ b ∧ hasPrivilege a ∧ hasPrivilege b)
} by bmc

unsat trace [bounded_safety] {
  any 10 actions
  assert ¬ at_least_one_privilege
} by { bmc }
-/

end DijkstraRing

veil module DijkstraRing

variable [FinEnum node] [insta : DecidableRel ring.next]

#gen_computable
#gen_executable

simple_deriving_repr_for State

deriving instance Repr for Label
deriving instance Repr for Reader
deriving instance Inhabited for Label
deriving instance Inhabited for State
deriving instance Inhabited for Reader

end DijkstraRing

#deriveGen DijkstraRing.Label

def simple_init (n : Nat) :=
  DijkstraRing.initExec (Fin n.succ.succ) (node_ne := ⟨0, Nat.zero_lt_succ _⟩)
    (DijkstraRing.State _) (DijkstraRing.Reader _)
    (insta := by dsimp [FiniteRing.next] ; infer_instance)

def DivM.run (a : DivM α) :=
  match a with
  | .res x => Option.some x
  | .div => Option.none

def DijkstraRing.defaultInitState {n : Nat} : DijkstraRing.State (Fin n.succ.succ) :=
  { x := fun _ => false, up := fun _ => false }

def simple_init' (n : Nat) :=
  simple_init n |>.run ⟨⟩ |>.run DijkstraRing.defaultInitState
    |>.run |>.run |>.getD (Except.ok ((), DijkstraRing.defaultInitState))
    |>.getD (fun _ => ((), DijkstraRing.defaultInitState)) |>.snd

def simple_run (n : Nat) :=
  DijkstraRing.nextActExec (Fin n.succ.succ) (node_ne := ⟨0, Nat.zero_lt_succ _⟩)
    (DijkstraRing.State _) (DijkstraRing.Reader _)
    (insta := by dsimp [FiniteRing.next] ; infer_instance)

def simple_check {n : Nat} (s₀ : _) (steps : Nat) (cfg : Plausible.Configuration) :=
  @check_safety _ _ _
    (sys := DijkstraRing.System (Fin n.succ.succ) (node_ne := ⟨0, Nat.zero_lt_succ _⟩)
      (DijkstraRing.State _) (DijkstraRing.Reader _))
    DijkstraRing.Label.gen (simple_run n) ⟨⟩ s₀ steps cfg
    (by intro r s ; dsimp [invSimp] ; dsimp [FiniteRing.next] ; infer_instance)

def simple_check' (n : Nat) (steps : Nat) (cfg : Plausible.Configuration) :=
  simple_check (simple_init' n) steps cfg

#eval simple_check' 2 100 ({ } : Plausible.Configuration) |>.run 1000
