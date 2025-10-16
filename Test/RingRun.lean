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
relation useless : node → node → node → node → Bool
-- veil_change
#gen_state

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
  useless A sender C next := pending C A
}

safety [single_leader] leader L → le N L
-- invariant pending S D ∧ btw S N D → le N S
invariant pending L L → le N L

#gen_spec

-- a syntax for filling sort arguments
open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

-- #time #check_invariants
section

veil_variables

omit χ χ_rep χ_rep_lawful

open Veil Extract

variable [FinEnum node] [Hashable node]
-- variable [insta : DecidableRel tot.le] -- [∀ a b c, Decidable (btwn.btw a b c)]

def instFinEnumForComponents (f : State.Label)
  : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    infer_instance_for_iterated_prod

instance instDecidableEqForComponents' (f : State.Label)
  : DecidableEq (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instDecidableEqForComponents'' (f : State.Label)
  : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents (f : State.Label)
  : Hashable (IteratedProd <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, List.foldr, State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents' (f : State.Label)
  : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

structure FourNodes where
  a : node
  b : node
  c : node
  d : node
deriving DecidableEq, Repr, Inhabited, Nonempty, Hashable

def FourNodes.equiv_IteratedProd :
  IteratedProd ((⌞? State.Label.toDomain ⌟) State.Label.useless) ≃
  FourNodes node where
  toFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1⟩
  invFun p := (p.a, (p.b, (p.c, (p.d, ()))))

-- need to use `abbrev` to allow typeclass inference
abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  | State.Label.leader => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.leader)
  | State.Label.pending => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.pending)
  | State.Label.useless => Std.HashSet (⌞? FourNodes ⌟)

instance instReprForComponents [Repr node] (f : State.Label)
  : Repr ((⌞? FieldConcreteType ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, IteratedProd', List.foldr, FieldConcreteType, State.Label.toDomain] <;>
    infer_instance

-- #simp [FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] FieldConcreteType Nat .leader
  -- Veil.CanonicalField (State.Label.toDomain Nat .pending) (State.Label.toCodomain Nat .pending)

instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
  constructor ; constructor <;> exact default

instance rep (f : State.Label) : FieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.leader =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.leader)
  | State.Label.pending =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.pending)
  | State.Label.useless =>
    instFinsetLikeAsFieldRep (⌞? FourNodes.equiv_IteratedProd ⌟) ((⌞? instFinEnumForComponents ⌟) State.Label.useless)

instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.leader =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.leader)
  | State.Label.pending =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.pending)
  | State.Label.useless =>
    instFinsetLikeLawfulFieldRep (⌞? FourNodes.equiv_IteratedProd ⌟) ((⌞? instFinEnumForComponents ⌟) State.Label.useless)

end

-- code optimization by controlled `dsimp`
-- set_option trace.Compiler.result true in
attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  FourNodes.equiv_IteratedProd
  instFinEnumForComponents in
-- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
#specialize_nextact with FieldConcreteType
  injection_begin [FinEnum node] [Hashable node] injection_end => NextAct'

#print NextAct'

simple_deriving_repr_for' State

deriving instance Repr for Label
-- deriving instance Inhabited for Label
-- deriving instance Inhabited for State
-- deriving instance Inhabited for Reader

#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin [FinEnum node] [Hashable node] injection_end

end Ring

namespace Ring

variable {n_node : Nat}

local macro "⌞ " t:term " ⌟" : term =>
  `(($t (Fin n_node.succ)))

local macro "⌞State⌟" : term =>
  `(((⌞ State ⌟) ⌞ FieldConcreteType ⌟))

local macro "⌞_ " t:term " _⌟" : term =>
  `((⌞ $t (⌞ Theory ⌟) (⌞State⌟) ⌟))

local macro "⌞__ " t:term " __⌟" : term =>
  `((⌞ $t (⌞ Theory ⌟) (⌞State⌟) ⌟) ⌞ FieldConcreteType ⌟)

local instance (n : Nat) : DecidableRel (TotalOrder.le (t := Fin n.succ)) := by
  dsimp [TotalOrder.le] ; infer_instance

def initState : ⌞State⌟ := default

def afterInit (r₀ : ⌞ Theory ⌟) (s₀ : ⌞State⌟) :=
  ⌞__ initMultiExec __⌟ |>.run r₀ |>.run s₀

def allResults (r₀ : ⌞ Theory ⌟) (s₀ : ⌞State⌟) (l : ⌞ Label ⌟) :=
  ⌞_ nextActMultiExec _⌟ l r₀ s₀

instance : Repr (State (Fin (Nat.succ 2)) (FieldConcreteType (Fin (Nat.succ 2)))) := by
  infer_instance

#time #eval @allResults 2 {} initState (Label.send 0 0)

end Ring
