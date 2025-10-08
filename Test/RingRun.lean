import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract

-- https://github.com/aman-goel/ivybench/blob/5db7eccb5c3bc2dd14dfb58eddb859b036d699f5/ex/ivy/ring.ivy

veil module Ring


type node
instantiate tot : TotalOrder node
-- instantiate btwn : Between node


open Between TotalOrder

relation leader : node -> Bool
relation pending (a : node) (b : node) : Bool
-- veil_change
#gen_state

-- __IMPORTANT: add this before writing any action/invariant__
set_option pp.explicit true
set_option pp.instances true

after_init {
  leader N := false
  pending M N := false
}

action send (n next : node) {
  -- require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

action recv (sender n next : node) {
  -- require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  -- message may or may not be removed
  -- this models that multiple messages might be in flight
  pending := *
  if (sender = n) then
    leader n := true
  else
    -- pass message to next node
    if (le n sender) then
      pending sender next := true
}

safety [single_leader] leader L → le N L
-- invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec

open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

-- #time #check_invariants
section

veil_variables

omit χ χ_rep χ_rep_lawful

open Veil

variable [FinEnum node] [Hashable node]
-- variable [insta : DecidableRel tot.le] -- [∀ a b c, Decidable (btwn.btw a b c)]

def instFinEnumForComponents (f : State.Label)
  : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toComponents ⌟) f) := by
  cases f <;>
    infer_instance_for_iterated_prod

instance instDecidableEqForComponents' (f : State.Label)
  : DecidableEq (IteratedProd <| (⌞? State.Label.toComponents ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toComponents] <;>
    infer_instance

instance instHashableForComponents (f : State.Label)
  : Hashable (IteratedProd <| (⌞? State.Label.toComponents ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toComponents] <;>
    infer_instance

-- need to use `abbrev` to allow typeclass inference
abbrev FieldConcreteType (f : State.Label) : Type :=
  Std.HashSet (IteratedProd <| (⌞? State.Label.toComponents ⌟) f)

instance instReprForComponents [Repr node] (f : State.Label)
  : Repr ((⌞? FieldConcreteType ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, FieldConcreteType, State.Label.toComponents] <;>
    infer_instance

-- #simp [FieldConcreteType, State.Label.toComponents, State.Label.toBase] FieldConcreteType Nat .leader
  -- Veil.CanonicalField (State.Label.toComponents Nat .pending) (State.Label.toBase Nat .pending)

instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
  constructor ; constructor <;> exact default

instance rep (f : State.Label) : FieldRepresentation
  ((⌞? State.Label.toComponents ⌟) f)
  ((⌞? State.Label.toBase ⌟) f)
  ((⌞? FieldConcreteType ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.leader =>
    instFinsetLikeAsFieldRep ((⌞? instFinEnumForComponents ⌟) State.Label.leader)
  | State.Label.pending =>
    instFinsetLikeAsFieldRep ((⌞? instFinEnumForComponents ⌟) State.Label.pending)

instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toComponents ⌟) f)
  ((⌞? State.Label.toBase ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.leader =>
    instFinsetLikeLawfulFieldRep ((⌞? instFinEnumForComponents ⌟) State.Label.leader)
  | State.Label.pending =>
    instFinsetLikeLawfulFieldRep ((⌞? instFinEnumForComponents ⌟) State.Label.pending)

end

set_option pp.explicit false
set_option pp.instances false

open Lean Meta Elab Term Command Veil in
run_cmd do
  let fnName ← liftCoreM <| realizeGlobalConstNoOverloadCore ``State.leader
  let fnInfo ← getConstInfo fnName
  logInfo m!"{fnInfo.type}"

#check (type_of% (@State.leader Nat (fun _ => Nat)))
-- simple_deriving_repr_for Theory
set_option trace.veil.desugar true
set_option trace.veil.debug true
simple_deriving_repr_for' State

deriving instance Repr for Label
-- deriving instance Inhabited for Label
-- deriving instance Inhabited for State
-- deriving instance Inhabited for Reader

set_option trace.veil.desugar true
#time #gen_executable_list! Std.Format
  injection_begin [FinEnum node] injection_end

-- #print initMultiExec
-- #print nextMultiExtract
-- #print nextActMultiExec

end Ring

namespace Ring

variable {n_node : Nat}

local macro "⌞ " t:term " ⌟" : term =>
  `(($t (Fin n_node.succ)))

local macro "⌞State⌟" : term =>
  `(((⌞ State ⌟) ⌞ FieldConcreteType ⌟))

local macro "⌞_ " t:term " _⌟" : term =>
  `((⌞ $t (⌞ Theory ⌟) (⌞State⌟) ⌟) ⌞ FieldConcreteType ⌟)

local instance (n : Nat) : DecidableRel (TotalOrder.le (t := Fin n.succ)) := by
  dsimp [TotalOrder.le] ; infer_instance

def initState : ⌞State⌟ := default

def afterInit (r₀ : ⌞ Theory ⌟) (s₀ : ⌞State⌟) :=
  ⌞_ initMultiExec _⌟ |>.run r₀ |>.run s₀

def allResults (r₀ : ⌞ Theory ⌟) (s₀ : ⌞State⌟) (l : ⌞ Label ⌟) :=
  ⌞_ nextActMultiExec _⌟ l r₀ s₀

instance : Repr (State (Fin (Nat.succ 2)) (FieldConcreteType (Fin (Nat.succ 2)))) := by
  infer_instance

instance : Repr (State (Fin (Nat.succ 2)) (FieldConcreteType (Fin (Nat.succ 2)))) := by
  infer_instance

#eval @allResults 2 {} initState (Label.send 0 0) |>.map Prod.fst
#eval @allResults 2 {} initState (Label.send 0 0) |>.map Prod.snd

end Ring
