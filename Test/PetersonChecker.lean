import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

veil module Peterson
-- ------------------------------- MODULE Peterson -------------------------------
-- (*****************************************************************************)
-- (* This module contains the specification for Peterson's Algorithm, taken    *)
-- (* from the "Parallel Programming" course taught at ULiège.                  *)
-- (* The invariant `Inv` is the one presented in the course augmented by a     *)
-- (* clause representing mutual exclusion of the critical section              *)
-- (* A proof is given to show that `Inv` is inductive.                         *)
-- (* Moreover the refinement from Peterson to the abstract lock is also proven.*)
-- (*****************************************************************************)

-- EXTENDS Integers, TLAPS

-- Other(p) == IF p = 1 THEN 2 ELSE 1

-- (*
-- --algorithm Peterson{
--     variables
--       c = [self \in ProcSet |-> FALSE],
--       turn = 1;

--     process(proc \in 1..2){
-- a0:   while(TRUE){
--         skip;
-- a1:     c[self] := TRUE;
-- a2:     turn := Other(self);
-- a3:     await ~c[Other(self)] \/ turn = self;
-- cs:     skip;
-- a4:     c[self] := FALSE;
--       }
--     }
-- }
-- *)
enum pc_state = { a0, a1, a2, a3, cs, a4 }
enum process = { P1, P2 }

individual turn : process
relation c : process → Bool
relation pc : process → pc_state → Bool
#gen_state


after_init  {
  c P := false
  turn := *
  pc P S := decide $ S = a0

}

action evtA0 (self : process)  {
  require pc self a0
  pc self S := decide $ S = a1
}

#print evtA0.do

action evtA1 (self : process)  {
  require pc self a1
  c self := true
  pc self S := decide $ S = a2
}

action evtA2 (self : process)  {
  require pc self a2
  turn := if self = P1 then P2 else P1
  pc self S := decide $ S = a3
}


action evtA3 (self : process)  {
  require pc self a3
  require ¬ c (if self = P1 then P2 else P1) ∨ turn = self
  pc self S := decide $ S = cs
}


action evtCS (self : process) {
  require pc self cs
  pc self S := decide $ S = a4
}

action evtA4 (self : process) {
  require pc self a4
  c self := false
  pc self S := decide $ S = a0
  -- pc self S := decide $ S = a4   -- Introduce an error here
}


invariant [pc_total] pc P a0 ∨ pc P a1 ∨ pc P a2 ∨ pc P a3 ∨ pc P cs ∨ pc P a4
invariant [unique_pc] pc P S ∧ pc P T → S = T

invariant [Inv_P1]
  ∀p, c p ↔ (pc p a2 ∨ pc p a3 ∨ pc p cs ∨ pc p a4)

ghost relation lockcs (i : process) := pc i cs ∨ pc i a4

invariant [Inv_P2]
  ∀p, (pc p cs ∨ pc p a4) →
  (turn = p ∨
    (pc (if p = P1 then P2 else P1) a0 ∨
     pc (if p = P1 then P2 else P1) a1 ∨
     pc (if p = P1 then P2 else P1) a2))

invariant [Inv_P3]
  ∀ i j, i ≠ j → ¬((pc i cs ∨ pc i a4) ∧ (pc j cs ∨ pc j a4))


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

open Veil


variable [FinEnum process] [Hashable process]
variable [FinEnum pc_state] [Hashable pc_state]
variable [Ord process] [Ord pc_state]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
variable [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord pc_state)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord pc_state)))]

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


-- instance [Ord α] : Ord (Array α) where
--   compare a b :=
--     a.zip b |>.foldl (init := Ordering.eq) fun c (a, b) => match c with
--       | Ordering.eq => compare a b
--       | c => c

instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := match x, y with
    | (a, b), (a', b') => compare a a' |>.then (compare b b')

instance instOrderForComponents' (f : State.Label)
  : Ord (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  | State.Label.turn => ((⌞? State.Label.toCodomain ⌟) State.Label.turn)
  | State.Label.c => Std.TreeSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.c)
  | State.Label.pc => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.pc)

instance instReprForComponents [Repr process] [Repr pc_state] (f : State.Label)
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
  | State.Label.c =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.c)
  | State.Label.pc =>
    instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.pc)
  | State.Label.turn => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain] ;
      infer_instance

instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
  | State.Label.c =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.c)
  | State.Label.pc =>
    instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.pc)
  | State.Label.turn => by
      dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, rep, id]
      infer_instance

end

attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  instFinEnumForComponents in
#specialize_nextact with FieldConcreteType
  injection_begin
    [FinEnum process] [Hashable process] [Ord process]
    [FinEnum pc_state] [Hashable pc_state] [Ord pc_state]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord pc_state)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord pc_state)))]
  injection_end => NextAct'

#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
    [FinEnum process] [Hashable process] [Ord process]
    [FinEnum pc_state] [Hashable pc_state] [Ord pc_state]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process)))]
    [Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord pc_state)))] [Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord pc_state)))]
  injection_end

deriving_enum_instance_for process
deriving_enum_instance_for pc_state

instance : Ord process where
  compare s1 s2 :=
    compare (s1.toCtorIdx) (s2.toCtorIdx)

instance : Ord pc_state where
  compare s1 s2 :=
    compare (s1.toCtorIdx) (s2.toCtorIdx)


instance : Hashable pc_state where
  hash s := hash s.toCtorIdx

instance : Hashable process where
  hash s := hash s.toCtorIdx


instance: BEq (FieldConcreteType pc_state process State.Label.turn) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain] ;
  infer_instance

instance: Hashable (FieldConcreteType pc_state process State.Label.turn) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain] ;
  infer_instance

instance [Hashable α] [BEq α] [Ord α] : Hashable (Std.TreeSet α) where
  hash s :=
    /- `Hash collision `-/
    s.foldl (init := 0) fun acc a => (hash (a, acc))

instance : Hashable (FieldConcreteType pc_state process State.Label.c) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance : Std.ReflCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))) := by
  apply Std.ReflCmp.mk
  unfold compare
  intro a; cases a <;> rfl

instance : Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))):= by
  apply Std.LawfulEqCmp.mk
  unfold compare inferInstanceAs instOrdPc_state
  intro a b; cases a <;>
    cases b <;> simp

instance : Std.ReflCmp (Ord.compare (self := inferInstanceAs (Ord process))) := by
  apply Std.ReflCmp.mk
  unfold compare
  intro a; cases a <;> rfl

instance : Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord process))):= by
  apply Std.LawfulEqCmp.mk
  unfold compare inferInstanceAs instOrdProcess
  intro a b; cases a <;>
    cases b <;> simp


instance :  Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))) := by
  apply Std.OrientedCmp.mk
  unfold compare inferInstanceAs instOrdPc_state
  intro a b; cases a <;>
    cases b <;> rfl


instance : Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord pc_state))) := by
  apply Std.TransCmp.mk
  unfold compare inferInstanceAs instOrdPc_state pc_state.toCtorIdx
  decide

instance : Std.OrientedCmp (Ord.compare (self := inferInstanceAs (Ord process))) := by
  apply Std.OrientedCmp.mk
  unfold compare inferInstanceAs instOrdProcess
  intro a b; cases a <;>
    cases b <;> rfl

instance : Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord process))) := by
  apply Std.TransCmp.mk
  unfold compare inferInstanceAs instOrdProcess
  decide
  -- intro a b c; cases a <;>
  --   cases b <;>
  --     cases c <;> simp_all

#Concretize pc_state, process

instance [Ord process] : BEq (Std.TreeSet process) where
  beq s1 s2 :=
    s1.toArray == s2.toArray

instance : BEq (FieldConcreteType pc_state process State.Label.c) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance

instance [Hashable α] [BEq α] : Hashable (Std.HashSet α) where
  hash s :=
    /- `Hash collision `-/
    s.fold (init := 0) fun acc a => acc + (hash a)

instance : Hashable (FieldConcreteType pc_state process State.Label.pc) := by
  dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
  infer_instance


#assembleInsts

instance : (rd : TheoryConcrete) → (st : StateConcrete) → Decidable ((fun ρ σ => Inv_P1 ρ σ) rd st) := by
  intro rd st
  dsimp [Inv_P1, FieldConcreteType, State.Label.toDomain, State.Label.toCodomain]
  infer_instance

simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory


instance : (rd : TheoryConcrete) → (st : StateConcrete) → Decidable ((fun ρ σ => Inv_P3 ρ σ) rd st) := by
  intro rd st
  dsimp [Inv_P3, FieldConcreteType, State.Label.toDomain, State.Label.toCodomain]
  infer_instance

simple_deriving_repr_for' State
deriving instance Repr for Label
deriving instance Inhabited for Theory



def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList (fun ρ σ => true) {} id).snd
#time #eval modelCheckerResult'
#html createExpandedGraphDisplay (collectTrace modelCheckerResult').1 (collectTrace modelCheckerResult').2



end Peterson
