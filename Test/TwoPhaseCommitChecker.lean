import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main


-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/two_phase_commit.ivy

veil module TwoPhaseCommit

type node
relation vote_yes : node -> Bool
relation vote_no : node -> Bool
relation alive : node -> Bool
relation go_commit : node -> Bool
relation go_abort : node -> Bool
relation decide_commit : node -> Bool
relation decide_abort : node -> Bool
individual abort_flag : Bool
immutable individual one : node

#gen_state

after_init {
  vote_yes N := false;
  vote_no N := false;
  alive N := true;
  go_commit N := false;
  go_abort N := false;
  decide_commit N := false;
  decide_abort N := false;
  abort_flag := false
}

action vote1 (n : node) {
  require alive n;
  require ¬vote_no n;
  require ¬decide_commit n;
  require ¬decide_abort n;
  vote_yes n := true
}

action vote2(n: node) {
  require alive n;
  require ¬vote_yes n;
  require ¬decide_commit n;
  require ¬decide_abort n;
  vote_no n := true;
  abort_flag := true;
  decide_abort n := true
}

action fail(n: node) {
  require alive n;
  alive n := false;
  abort_flag := true
}

action go1 {
  require ∀ N, ¬go_commit N;
  require ∀ N, ¬go_abort N;
  require ∀ N, vote_yes N;
  go_commit N := true
}

action go2 {
  require ∀ N, ¬go_commit N;
  require ∀ N, ¬go_abort N;
  require exists n, vote_no n ∨ ¬alive n;
  go_abort N := true
}

action commit(n: node) {
  require alive n;
  require go_commit n;
  decide_commit n := true
}

action abort(n: node) {
  require alive n;
  require go_abort n;
  decide_abort n := true
}

safety (decide_commit N → ¬decide_abort N2) ∧ (decide_commit N -> vote_yes N2) ∧ (decide_abort N → abort_flag)
invariant [manual_1] ¬((¬(alive N) ∧ ¬(abort_flag)))
invariant [manual_2] ¬((¬(abort_flag) ∧ vote_no N))
invariant [manual_3] ¬((¬(abort_flag) ∧ go_abort N))
invariant [manual_4] ¬((¬(go_abort N) ∧ decide_abort N ∧ vote_yes N))
invariant [manual_5] ¬((¬(go_commit N) ∧ decide_commit N))
invariant [manual_6] (N0 ≠ N1) -> ¬((¬(go_commit N0) ∧ go_commit N1))
invariant [manual_7] ¬((¬(vote_yes N) ∧ go_commit N))
invariant [manual_8] ¬((go_commit N ∧ go_abort N))
invariant [trivial_1] ¬(∃n, decide_commit n)

#gen_spec

-- a syntax for filling sort arguments
open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

#time #check_invariants
section

veil_variables

omit χ χ_rep χ_rep_lawful

open Veil Extract

variable [FinEnum node] [Hashable node]


def instFinEnumForComponents (f : State.Label)
  : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    infer_instance_for_iterated_prod

instance instDecidableEqForComponents'' (f : State.Label)
  : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents' (f : State.Label)
  : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance


abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  | State.Label.abort_flag => ((⌞? State.Label.toCodomain ⌟) State.Label.abort_flag)
  | State.Label.vote_yes => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.vote_yes)
  | State.Label.vote_no => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.vote_no)
  | State.Label.alive => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.alive)
  | State.Label.go_commit => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.go_commit)
  | State.Label.go_abort => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.go_abort)
  | State.Label.decide_commit => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.decide_commit)
  | State.Label.decide_abort => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.decide_abort)

instance instReprForComponents [Repr node] (f : State.Label)
  : Repr ((⌞? FieldConcreteType ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance

instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
  constructor ; constructor <;>
  dsimp only [FieldConcreteType, State.Label.toCodomain] <;>
  exact default

instance rep (f : State.Label) : FieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.abort_flag => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance
  | State.Label.vote_yes =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.vote_yes)
  | State.Label.vote_no =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.vote_no)
  | State.Label.alive =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.alive)
  | State.Label.go_commit =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.go_commit)
  | State.Label.go_abort =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.go_abort)
  | State.Label.decide_commit =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.decide_commit)
  | State.Label.decide_abort =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.decide_abort)


instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.abort_flag => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance
  | State.Label.vote_yes =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.vote_yes)
  | State.Label.vote_no =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.vote_no)
  | State.Label.alive =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.alive)
  | State.Label.go_commit =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.go_commit)
  | State.Label.go_abort =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.go_abort)
  | State.Label.decide_commit =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.decide_commit)
  | State.Label.decide_abort =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.decide_abort)

end

attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  instFinEnumForComponents in
-- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
#specialize_nextact with FieldConcreteType
  injection_begin
    [FinEnum node] [Hashable node]
  injection_end => NextAct'

#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
    [FinEnum node] [Hashable node]
  injection_end


#Concretize (Fin 1)


instance [FinEnum α] [Hashable α] : BEq (FieldConcreteType α State.Label.abort_flag) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain] ;
  infer_instance

instance [FinEnum α] [Hashable α] : Hashable (FieldConcreteType α State.Label.abort_flag) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain] ;
  infer_instance

instance [Hashable α] [BEq α] : Hashable (Std.HashSet α) where
  hash s :=
    /- `Hash collision `-/
    s.fold (init := 0) fun acc a => acc + (hash a)

#assembleInsts

instance : (rd : TheoryConcrete) → (st : StateConcrete) → Decidable ((fun ρ σ => manual_1 ρ σ) rd st) := by
  intro rd st
  dsimp [manual_1, FieldConcreteType, State.Label.toDomain, State.Label.toCodomain]
  infer_instance


simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory

def modelCheckerResult' := (runModelCheckerx {one := 1} labelList initVeilMultiExecM nextVeilMultiExecM (fun ρ σ => manual_1 ρ σ)).snd
#time #eval modelCheckerResult'.seen.length




end TwoPhaseCommit
