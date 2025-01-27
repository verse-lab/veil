import Aesop
import Mathlib.Data.Set.Basic

-- CHECK come from the "longer" file
class PersonalQuorums {Node : Type u} (quorum_of : Node → Set Node → Prop) where
  quorum_assm : ∀ p p' Q, quorum_of p Q → p' ∈ Q → quorum_of p' Q

-- CHECK come from the "longer" file
namespace PersonalQuorums

variable {Node : Type u} (quorum_of : Node → Set Node → Prop)
open PersonalQuorums

def quorum_of_set (S Q : Set Node) : Prop := ∃ p ∈ S, quorum_of p Q

-- NOTE: this definition is the same as the one in the DISC'19 paper,
-- but different from the one in the FMBC'20 paper!
-- in the FMBC'20 paper, the conclusion should be like `S ∩ Q ∩ Q' ≠ ∅`
def is_intertwined (W S : Set Node) : Prop :=
  S ⊆ W ∧ (∀ Q Q', quorum_of_set quorum_of S Q → quorum_of_set quorum_of S Q' → W ∩ Q ∩ Q' ≠ ∅)

-- simply by definition
lemma qi_intertwined (W S Q1 Q2 : Set Node) (n1 n2 : Node) :
  is_intertwined quorum_of W S → n1 ∈ S → n2 ∈ S →
  quorum_of n1 Q1 → quorum_of n2 Q2 →
  ∃ n3, n3 ∈ W ∧ n3 ∈ Q1 ∧ n3 ∈ Q2 := by
  unfold is_intertwined quorum_of_set
  simp only [forall_exists_index, and_imp]
  intro h1 h2 h3 h4 h5 h6
  specialize h2 _ _ _ h3 h5 _ h4 h6
  rewrite [← Set.nonempty_iff_ne_empty] at h2
  cases h2 ; aesop

end PersonalQuorums

namespace StellarQuorums

def project {α β : Type} (slices : β → Set (Set α)) (S : Set α) : β → Set (Set α) :=
  fun n => { Sl ∩ S | Sl ∈ slices n }

-- FIXME: might be better to lift `Node` as an argument?
class System where
  Node : Type
  /-- The set of well-behaved nodes. -/
  W : Set Node
  slices : Node → Set (Set Node)
  slices_ne : ∀ p ∈ W, slices p ≠ ∅

def project_system (s : System) (I : Set s.Node) : System :=
  { Node := s.Node
    W := s.W
    slices := project s.slices I
    slices_ne := by
      unfold project
      have h := s.slices_ne
      intro p hin ; specialize h _ hin
      rewrite [← Set.nonempty_iff_ne_empty] at h ⊢
      rcases h with ⟨Sl, h⟩ ; constructor ; aesop }

variable [inst : System]
open System

def quorum (Q : Set Node) : Prop := ∀ p ∈ Q ∩ W, ∃ Sl ∈ slices p, Sl ⊆ Q

lemma quorum_after_proj (Q I : Set Node) : quorum (inst := inst) Q → quorum (inst := project_system inst I) Q := by
  rcases inst with ⟨Node, W, slices, slices_ne⟩
  unfold quorum project_system project ; simp
  intro hq p h1 h2 ; specialize hq _ h1 h2 ; rcases hq with ⟨Sl, hq1, hq2⟩
  exists Sl ; apply And.intro ; assumption
  rw [Set.subset_def] at hq2 ⊢ ; simp ; aesop     -- well, just by def

-- CHECK come from the "longer" file
def quorum_of (p : Node) (Q : Set Node) : Prop := quorum Q ∧ (p ∉ W ∨ (∃ Sl ∈ slices p, Sl ⊆ Q))

lemma quorum_of_add_self (p : Node) (Q : Set Node) : quorum_of p Q → quorum (Q ∪ { p }) := by
  intro ⟨hq, ha⟩ ; simp only [quorum, Set.mem_inter_iff, and_imp, Set.mem_insert_iff, forall_eq_or_imp] at hq ⊢
  intro q hb hc ; simp at hb
  cases hb with
  | inl heq =>
    cases ha with
    | inl ha => subst_vars ; contradiction
    | inr ha => subst_vars ; rcases ha with ⟨Sl, hq1, hq2⟩ ; exists Sl ; solve_by_elim [Set.subset_union_of_subset_left]
  | inr h => specialize hq _ h hc ; rcases hq with ⟨Sl, hq1, hq2⟩ ; exists Sl ; solve_by_elim [Set.subset_union_of_subset_left]

instance : PersonalQuorums quorum_of where
  quorum_assm := by
    unfold quorum_of quorum ; simp
    intro p p' Q h1 h2 h3
    apply And.intro ; exact h1
    by_cases p' ∈ W <;> aesop

-- CHECK come from the "longer" file
lemma quorum_union : quorum Q → quorum Q' → quorum (Q ∪ Q') := by
  unfold quorum ; simp
  -- FIXME: well, `aesop` cannot handle it. why?
  intro ha hb p hor hw ; cases hor with
  | inl hor => specialize ha _ hor hw ; aesop (add unsafe apply Set.subset_union_of_subset_left)
  | inr hor => specialize hb _ hor hw ; aesop (add unsafe apply Set.subset_union_of_subset_right)

-- NOTE: this definition is different from the one on the paper!
def is_intact (I : Set Node) : Prop :=
  I ⊆ W ∧ quorum (inst := inst) I ∧
    (∀ Q Q', quorum (inst := project_system inst I) Q → quorum (inst := project_system inst I) Q' →
      Q ∩ I ≠ ∅ → Q' ∩ I ≠ ∅ → Q ∩ Q' ∩ I ≠ ∅)

open PersonalQuorums

lemma intact_set_is_intertwined (I : Set Node) : is_intact I → is_intertwined quorum_of W I := by
  unfold is_intact is_intertwined quorum_of_set
  simp only [forall_exists_index, and_imp]
  intro h1 h2 h3
  apply And.intro ; apply h1
  intro Q Q' x hin hq x' hin' hq'
  have ha := quorum_of_add_self _ _ hq
  have ha' := quorum_of_add_self _ _ hq'
  specialize h3 _ _ (quorum_after_proj _ _ ha) (quorum_after_proj _ _ ha')
  sorry

-- -- fix an intact set, and an
-- variable (I : { I : Set Node // is_intact I })
-- variable (S : { S : Set Node // is_intertwined quorum_of W S })

-- lemma intact_intertwined (n : Node) : n ∈ I.val → n ∈ S.val := by
--   rcases I with ⟨I, hI⟩ ; rcases S with ⟨S, hS⟩

-- lemma qi_intertwined (S Q1 Q2 : Set Node) (n1 n2 : Node) :
--   is_intertwined quorum_of W S → n1 ∈ S → n2 ∈ S →
--   quorum_of n1 Q1 → quorum_of n2 Q2 →
--   ∃ n3, n3 ∈ W ∧ n3 ∈ Q1 ∧ n3 ∈ Q2 := by

end StellarQuorums
