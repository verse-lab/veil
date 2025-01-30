import Aesop
import Mathlib.Data.Set.Basic

-- adapted from [FBA.thy](https://github.com/stellar/scp-proofs/blob/ac41c6353fae870c47c0e7ee558da98c03a7d041/FBA.thy)

/-
  NOTE: For now we do not prove liveness property in Veil, so we only
  adapt the definitions that are sufficient for justifying the assumptions
  in the current Veil model of SCP.
-/

theorem Set.ne_empty_iff_exists_mem {α : Type u} {s : Set α} : s ≠ ∅ ↔ ∃ a, a ∈ s := by
  rw [← Set.nonempty_iff_ne_empty] ; aesop

namespace FBA

def project {α β : Type} (slices : β → Set (Set α)) (S : Set α) : β → Set (Set α) :=
  fun n => { Sl ∩ S | Sl ∈ slices n }

class System where
  Node : Type
  /-- The set of well-behaved nodes. -/
  W : Set Node
  slices : Node → Set (Set Node)
  /-- The set of slices of a well-behaved node is not empty. -/
  slices_ne : ∀ p ∈ W, slices p ≠ ∅

/-- Restrict all slices in `sys` to only include nodes from `I`.
    See how it is used in the definition of `intertwined`. -/
def System.project (sys : System) (I : Set sys.Node) : System :=
  { Node := sys.Node
    W := sys.W
    slices := FBA.project sys.slices I
    slices_ne := by
      intro p hin
      unfold FBA.project
      have h := sys.slices_ne _ hin
      rw [Set.ne_empty_iff_exists_mem] at h ⊢ ; aesop }

variable [inst : System]
open System

/-- A quorum is a set whose well-behaved members have at least one slice
    included in the set. -/
def quorum (Q : Set Node) : Prop := ∀ p ∈ Q ∩ W, ∃ Sl ∈ slices p, Sl ⊆ Q

/-- A set `S` is a slice-blocking set for a node `p` when every slice of
    `p` intersects `S`. -/
def blocks_slices (S : Set Node) (p : Node) : Prop :=
  ∀ Sl ∈ slices p, Sl ∩ S ≠ ∅

/-- A set of node is intertwined if all of its members are well-behaved
    and it satisfies the quorum intersection property. -/
structure intertwined (S : Set Node) where
  well_behaved : S ⊆ W
  /-- The quorum intersection property; `project`ing the system to `S`
      allows for the worst-case quorums that might arise.
      Check [the original FMBC'20 paper](https://drops.dagstuhl.de/storage/01oasics/oasics-vol084-fmbc2020/OASIcs.FMBC.2020.9/OASIcs.FMBC.2020.9.pdf) and
      [the DISC'19 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol146-disc2019/LIPIcs.DISC.2019.27/LIPIcs.DISC.2019.27.pdf)
      for more information. -/
  q_inter : (∀ Q Q',
    quorum (inst := inst.project S) Q →
    quorum (inst := inst.project S) Q' →
    Q ∩ S ≠ ∅ → Q' ∩ S ≠ ∅ → Q ∩ Q' ∩ S ≠ ∅)

/-- A set of node is intact if all of its members are well-behaved
    and it satisfies both the quorum availability property and
    the quorum intersection property. -/
structure intact (I : Set Node) extends intertwined I where
  /-- The quorum availability property: `I` itself is a quorum. -/
  q_avail : quorum (inst := inst) I

theorem intact_implies_intertwined : ∀ I, intact I → intertwined I := by
  intro I h ; cases h ; assumption

theorem intertwined_node_is_well_behaved : ∀ n S, intertwined S → n ∈ S → n ∈ W := by
  intro n S ⟨h, _⟩ ; aesop

theorem intact_node_is_well_behaved : ∀ n I, intact I → n ∈ I → n ∈ W := by
  intro n S h ; apply intertwined_node_is_well_behaved ; apply intact_implies_intertwined _ h

theorem slice_blocks_ne : ∀ n S I, intact I → n ∈ I → blocks_slices S n →
    S ∩ I ≠ ∅ := by
  intro n S I hI hin hblock
  unfold blocks_slices at hblock
  have h := hI.q_avail ; unfold quorum at h
  simp at h ; specialize h _ hin (intact_node_is_well_behaved _ _ hI hin)
  rcases h with ⟨Sl, hSl, h⟩ ; specialize hblock _ hSl
  rw [Set.ne_empty_iff_exists_mem] at hblock ⊢ ; simp at hblock ⊢
  aesop

end FBA

-- CHECK come from the "longer" file
-- class PersonalQuorums {Node : Type u} (quorum_of : Node → Set Node → Prop) where
--   quorum_assm : ∀ p p' Q, quorum_of p Q → p' ∈ Q → quorum_of p' Q

-- -- CHECK come from the "longer" file
-- namespace PersonalQuorums

-- variable {Node : Type u} (quorum_of : Node → Set Node → Prop)
-- open PersonalQuorums

-- def quorum_of_set (S Q : Set Node) : Prop := ∃ p ∈ S, quorum_of p Q

-- -- NOTE: this definition is the same as the one in the DISC'19 paper,
-- -- but different from the one in the FMBC'20 paper!
-- -- in the FMBC'20 paper, the conclusion should be like `S ∩ Q ∩ Q' ≠ ∅`
-- def is_intertwined (W S : Set Node) : Prop :=
--   S ⊆ W ∧ (∀ Q Q', quorum_of_set quorum_of S Q → quorum_of_set quorum_of S Q' → W ∩ Q ∩ Q' ≠ ∅)

-- -- simply by definition
-- lemma qi_intertwined (W S Q1 Q2 : Set Node) (n1 n2 : Node) :
--   is_intertwined quorum_of W S → n1 ∈ S → n2 ∈ S →
--   quorum_of n1 Q1 → quorum_of n2 Q2 →
--   ∃ n3, n3 ∈ W ∧ n3 ∈ Q1 ∧ n3 ∈ Q2 := by
--   unfold is_intertwined quorum_of_set
--   simp only [forall_exists_index, and_imp]
--   intro h1 h2 h3 h4 h5 h6
--   specialize h2 _ _ _ h3 h5 _ h4 h6
--   rewrite [← Set.nonempty_iff_ne_empty] at h2
--   cases h2 ; aesop

-- end PersonalQuorums

-- namespace StellarQuorums

-- def project {α β : Type} (slices : β → Set (Set α)) (S : Set α) : β → Set (Set α) :=
--   fun n => { Sl ∩ S | Sl ∈ slices n }

-- -- FIXME: might be better to lift `Node` as an argument?
-- class System where
--   Node : Type
--   /-- The set of well-behaved nodes. -/
--   W : Set Node
--   slices : Node → Set (Set Node)
--   slices_ne : ∀ p ∈ W, slices p ≠ ∅

-- def project_system (s : System) (I : Set s.Node) : System :=
--   { Node := s.Node
--     W := s.W
--     slices := project s.slices I
--     slices_ne := by
--       unfold project
--       have h := s.slices_ne
--       intro p hin ; specialize h _ hin
--       rewrite [← Set.nonempty_iff_ne_empty] at h ⊢
--       rcases h with ⟨Sl, h⟩ ; constructor ; aesop }

-- variable [inst : System]
-- open System

-- def quorum (Q : Set Node) : Prop := ∀ p ∈ Q ∩ W, ∃ Sl ∈ slices p, Sl ⊆ Q

-- lemma quorum_after_proj (Q I : Set Node) : quorum (inst := inst) Q → quorum (inst := project_system inst I) Q := by
--   rcases inst with ⟨Node, W, slices, slices_ne⟩
--   unfold quorum project_system project ; simp
--   intro hq p h1 h2 ; specialize hq _ h1 h2 ; rcases hq with ⟨Sl, hq1, hq2⟩
--   exists Sl ; apply And.intro ; assumption
--   rw [Set.subset_def] at hq2 ⊢ ; simp ; aesop     -- well, just by def

-- -- CHECK come from the "longer" file
-- def quorum_of (p : Node) (Q : Set Node) : Prop := quorum Q ∧ (p ∉ W ∨ (∃ Sl ∈ slices p, Sl ⊆ Q))

-- lemma quorum_of_add (p : Node) (Q : Set Node) : p ∈ Q → p ∈ W → quorum Q → quorum_of p Q := by
--   intro hp hw hq
--   unfold quorum_of
--   apply And.intro ; assumption
--   unfold quorum at hq
--   simp at hq ; specialize hq _ hp hw ; aesop

-- def def1 (W S : Set Node) : Prop :=
--   S ⊆ W ∧ (∀ Q Q', (∃ p ∈ S, quorum_of p Q) → (∃ p ∈ S, quorum_of p Q') → S ∩ Q ∩ Q' ≠ ∅)

-- def def2 (W S : Set Node) : Prop :=
--   S ⊆ W ∧ (∀ Q Q', quorum Q → quorum Q' → Q ∩ S ≠ ∅ → Q' ∩ S ≠ ∅ → S ∩ Q ∩ Q' ≠ ∅)

-- example : ∀ S, def1 W S → def2 W S := by
--   intro S ⟨ha, hb⟩
--   apply And.intro ; assumption
--   intro Q Q' hq hq' hi hi'
--   rw [← Set.nonempty_iff_ne_empty] at hi hi'
--   rcases hi with ⟨n, hi⟩ ; rcases hi' with ⟨n', hi'⟩
--   simp at hi hi'
--   rcases hi with ⟨hip, his⟩ ; rcases hi' with ⟨hip', his'⟩
--   simp at hb
--   have hiw : n ∈ W := by rw [Set.subset_def] at ha ; solve_by_elim
--   have hiw' : n' ∈ W := by rw [Set.subset_def] at ha ; solve_by_elim
--   specialize hb _ _ n his (quorum_of_add _ _ hip hiw hq) _ his' (quorum_of_add _ _ hip' hiw' hq')
--   assumption

-- example : ∀ S, def2 W S → def1 W S := by
--   intro S ⟨ha, hb⟩
--   apply And.intro ; assumption
--   intro Q Q' ⟨n, hiq, ⟨hq, hqq⟩⟩ ⟨n', hiq', ⟨hq', hqq'⟩⟩
--   have hiw : n ∈ W := by rw [Set.subset_def] at ha ; solve_by_elim
--   have hiw' : n' ∈ W := by rw [Set.subset_def] at ha ; solve_by_elim
--   rcases hqq with hqq | hqq ; contradiction
--   rcases hqq' with hqq' | hqq' ; contradiction
--   rw [← Set.nonempty_iff_ne_empty] at hi hi'
--   rcases hi with ⟨n, hi⟩ ; rcases hi' with ⟨n', hi'⟩
--   simp at hi hi'
--   rcases hi with ⟨hip, his⟩ ; rcases hi' with ⟨hip', his'⟩
--   simp at hb
--   have hiw : n ∈ W := by rw [Set.subset_def] at ha ; solve_by_elim
--   have hiw' : n' ∈ W := by rw [Set.subset_def] at ha ; solve_by_elim
--   specialize hb _ _ n his (quorum_of_add _ _ hip hiw hq) _ his' (quorum_of_add _ _ hip' hiw' hq')
--   assumption


-- lemma quorum_of_add_self (p : Node) (Q : Set Node) : quorum_of p Q → quorum (Q ∪ { p }) := by
--   intro ⟨hq, ha⟩ ; simp only [quorum, Set.mem_inter_iff, and_imp, Set.mem_insert_iff, forall_eq_or_imp] at hq ⊢
--   intro q hb hc ; simp at hb
--   cases hb with
--   | inl heq =>
--     cases ha with
--     | inl ha => subst_vars ; contradiction
--     | inr ha => subst_vars ; rcases ha with ⟨Sl, hq1, hq2⟩ ; exists Sl ; solve_by_elim [Set.subset_union_of_subset_left]
--   | inr h => specialize hq _ h hc ; rcases hq with ⟨Sl, hq1, hq2⟩ ; exists Sl ; solve_by_elim [Set.subset_union_of_subset_left]

-- instance : PersonalQuorums quorum_of where
--   quorum_assm := by
--     unfold quorum_of quorum ; simp
--     intro p p' Q h1 h2 h3
--     apply And.intro ; exact h1
--     by_cases p' ∈ W <;> aesop

-- -- CHECK come from the "longer" file
-- lemma quorum_union : quorum Q → quorum Q' → quorum (Q ∪ Q') := by
--   unfold quorum ; simp
--   -- FIXME: well, `aesop` cannot handle it. why?
--   intro ha hb p hor hw ; cases hor with
--   | inl hor => specialize ha _ hor hw ; aesop (add unsafe apply Set.subset_union_of_subset_left)
--   | inr hor => specialize hb _ hor hw ; aesop (add unsafe apply Set.subset_union_of_subset_right)

-- -- NOTE: this definition is different from the one on the paper!
-- def is_intact (I : Set Node) : Prop :=
--   I ⊆ W ∧ quorum (inst := inst) I ∧
--     (∀ Q Q', quorum (inst := project_system inst I) Q → quorum (inst := project_system inst I) Q' →
--       Q ∩ I ≠ ∅ → Q' ∩ I ≠ ∅ → Q ∩ Q' ∩ I ≠ ∅)

-- open PersonalQuorums

-- lemma intact_set_is_intertwined (I : Set Node) : is_intact I → is_intertwined quorum_of W I := by
--   unfold is_intact is_intertwined quorum_of_set
--   simp only [forall_exists_index, and_imp]
--   intro h1 h2 h3
--   apply And.intro ; apply h1
--   intro Q Q' x hin hq x' hin' hq'
--   have ha := quorum_of_add_self _ _ hq
--   have ha' := quorum_of_add_self _ _ hq'
--   specialize h3 _ _ (quorum_after_proj _ _ ha) (quorum_after_proj _ _ ha')
--   sorry

-- -- -- fix an intact set, and an
-- -- variable (I : { I : Set Node // is_intact I })
-- -- variable (S : { S : Set Node // is_intertwined quorum_of W S })

-- -- lemma intact_intertwined (n : Node) : n ∈ I.val → n ∈ S.val := by
-- --   rcases I with ⟨I, hI⟩ ; rcases S with ⟨S, hS⟩

-- -- lemma qi_intertwined (S Q1 Q2 : Set Node) (n1 n2 : Node) :
-- --   is_intertwined quorum_of W S → n1 ∈ S → n2 ∈ S →
-- --   quorum_of n1 Q1 → quorum_of n2 Q2 →
-- --   ∃ n3, n3 ∈ W ∧ n3 ∈ Q1 ∧ n3 ∈ Q2 := by

-- end StellarQuorums
