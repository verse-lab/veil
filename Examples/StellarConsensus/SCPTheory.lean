-- skip eval
import Mathlib.Data.Set.Basic

-- adapted from [FBA.thy](https://github.com/stellar/scp-proofs/blob/ac41c6353fae870c47c0e7ee558da98c03a7d041/FBA.thy)

namespace FBA

theorem set_ne_empty_iff_exists_mem {α : Type u} {s : Set α} : s ≠ ∅ ↔ ∃ a, a ∈ s := by
  rw [← Set.nonempty_iff_ne_empty]
  aesop

def project {α β : Type} (slices : β → Set (Set α)) (S : Set α) : β → Set (Set α) :=
  fun n => { Sl ∩ S | Sl ∈ slices n }

class System (Node : Type) where
  /-- The set of well-behaved nodes. -/
  W : Set Node
  slices : Node → Set (Set Node)
  /-- The set of slices of a well-behaved node is not empty. -/
  slices_ne : ∀ p ∈ W, slices p ≠ ∅

variable {Node : Type}

/-- Restrict all slices in `sys` to only include nodes from `I`.
    See how it is used in the definition of `intertwined`. -/
def System.project (sys : System Node) (I : Set Node) : System Node :=
  { W := sys.W
    slices := FBA.project sys.slices I
    slices_ne := by
      intro p hin
      unfold FBA.project
      have h := sys.slices_ne _ hin
      rw [set_ne_empty_iff_exists_mem] at h ⊢
      aesop }

variable [inst : System Node]
open System

/-- A quorum is a set whose well-behaved members have at least one slice
    included in the set. -/
def quorum (Q : Set Node) : Prop := ∀ p ∈ Q ∩ W, ∃ Sl ∈ slices p, Sl ⊆ Q

-- `System.project` allows more quorums.
theorem quorum_after_proj (Q S : Set Node) : quorum (inst := inst) Q → quorum (inst := inst.project S) Q := by
  rcases inst with ⟨W, slices, slices_ne⟩
  unfold quorum System.project FBA.project
  simp
  intro hq p h1 h2
  specialize hq _ h1 h2
  rcases hq with ⟨Sl, hq1, hq2⟩
  exists Sl
  apply And.intro
  · assumption
  · rw [Set.subset_def] at hq2 ⊢
    simp
    aesop

-- A quorum in a projection to a larger set is also a quorum in a projection
-- to any smaller set.
theorem quorum_project_subset {Q S T : Set Node} (hST : S ⊆ T) :
    quorum (inst := inst.project T) Q → quorum (inst := inst.project S) Q := by
  rcases inst with ⟨W, slices, slices_ne⟩
  unfold quorum System.project FBA.project
  simp
  intro hq p hpQ hpW
  specialize hq p hpQ hpW
  rcases hq with ⟨Sl, hSl, hSlQ⟩
  exists Sl
  constructor
  · assumption
  · intro x hx
    exact hSlQ ⟨hx.1, hST hx.2⟩

/-- A set `S` is a slice-blocking set for a node `p` when every slice of
    `p` intersects `S`. -/
def slice_blocking (S : Set Node) (p : Node) : Prop :=
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
  q_inter : ∀ Q Q',
    quorum (inst := inst.project S) Q →
    quorum (inst := inst.project S) Q' →
    Q ∩ S ≠ ∅ → Q' ∩ S ≠ ∅ → Q ∩ Q' ∩ S ≠ ∅

/-- A set of node is intact if all of its members are well-behaved
    and it satisfies both the quorum availability property and
    the quorum intersection property. -/
structure intact (I : Set Node) extends intertwined I where
  /-- The quorum availability property: `I` itself is a quorum. -/
  q_avail : quorum I

theorem intact_implies_intertwined : ∀ (I : Set Node), intact I → intertwined I := by
  intro I h
  cases h
  assumption

theorem intertwined_node_is_well_behaved : ∀ n (S : Set Node), intertwined S → n ∈ S → n ∈ W := by
  intro n S ⟨h, _⟩
  aesop

theorem intact_node_is_well_behaved : ∀ n (I : Set Node), intact I → n ∈ I → n ∈ W := by
  intro n S h
  apply intertwined_node_is_well_behaved
  apply intact_implies_intertwined _ h

theorem slice_blocks_ne : ∀ n (S I : Set Node), intact I → n ∈ I → slice_blocking S n →
    S ∩ I ≠ ∅ := by
  intro n S I hI hin hblock
  unfold slice_blocking at hblock
  have h := hI.q_avail
  unfold quorum at h
  simp at h
  specialize h _ hin (intact_node_is_well_behaved _ _ hI hin)
  rcases h with ⟨Sl, hSl, h⟩
  specialize hblock _ hSl
  rw [set_ne_empty_iff_exists_mem] at hblock ⊢
  simp at hblock ⊢
  aesop

/-- If `U` is a quorum intersecting an intact set `I`, and `U ⊆ S`, then
    either `S` contains all intact nodes, or some intact node outside `S` is
    blocked by the intact members already in `S`. -/
theorem cascade {U S I : Set Node}
    (hI : intact I)
    (hUq : quorum U)
    (hUint : U ∩ I ≠ ∅)
    (hUS : U ⊆ S) :
    I ⊆ S ∨ ∃ n ∈ I \ S, ∀ Sl ∈ slices n, Sl ∩ S ∩ I ≠ ∅ := by
  classical
  by_cases hIS : I ⊆ S
  · exact Or.inl hIS
  · right
    by_contra hblocked
    push_neg at hblocked
    have hdiff_quorum : quorum (inst := inst.project I) (I \ S) := by
      unfold quorum
      intro p hp
      rcases hp with ⟨⟨hpI, hpS⟩, _hpW⟩
      rcases hblocked p ⟨hpI, hpS⟩ with ⟨Sl, hSl, hSl_empty⟩
      refine ⟨Sl ∩ I, ?_, ?_⟩
      · unfold System.project FBA.project
        exact ⟨Sl, hSl, rfl⟩
      · intro x hx
        rcases hx with ⟨hxSl, hxI⟩
        refine ⟨hxI, ?_⟩
        intro hxS
        have hx_empty : x ∈ Sl ∩ S ∩ I := ⟨⟨hxSl, hxS⟩, hxI⟩
        rw [hSl_empty] at hx_empty
        exact hx_empty
    have hU_proj : quorum (inst := inst.project I) U :=
      quorum_after_proj (inst := inst) U I hUq
    have hdiff_inter : (I \ S) ∩ I ≠ ∅ := by
      rw [Set.subset_def] at hIS
      push_neg at hIS
      rw [set_ne_empty_iff_exists_mem]
      rcases hIS with ⟨n, hnI, hnS⟩
      exact ⟨n, ⟨⟨hnI, hnS⟩, hnI⟩⟩
    have hq_inter := hI.q_inter (I \ S) U hdiff_quorum hU_proj hdiff_inter hUint
    rw [set_ne_empty_iff_exists_mem] at hq_inter
    rcases hq_inter with ⟨n, ⟨⟨⟨_hnI, hnS⟩, hnU⟩, _⟩⟩
    exact hnS (hUS hnU)

theorem union_quorum {I1 I2 : Set Node}
    (hI1 : intact (inst := inst) I1)
    (hI2 : intact (inst := inst) I2) :
    quorum (inst := inst) (I1 ∪ I2) := by
  unfold quorum
  intro p hp
  rcases hp with ⟨hp_union, hpW⟩
  rcases hp_union with hpI1 | hpI2
  · have hq := hI1.q_avail
    unfold quorum at hq
    rcases hq p ⟨hpI1, hpW⟩ with ⟨Sl, hSl, hSlI1⟩
    refine ⟨Sl, hSl, ?_⟩
    intro x hx
    exact Or.inl (hSlI1 hx)
  · have hq := hI2.q_avail
    unfold quorum at hq
    rcases hq p ⟨hpI2, hpW⟩ with ⟨Sl, hSl, hSlI2⟩
    refine ⟨Sl, hSl, ?_⟩
    intro x hx
    exact Or.inr (hSlI2 hx)

theorem union_quorum_intersection {I1 I2 Q1 Q2 : Set Node}
    (hI1 : intact I1)
    (hI2 : intact I2)
    (hinter : I1 ∩ I2 ≠ ∅)
    (hQ1 : quorum (inst := inst.project (I1 ∪ I2)) Q1)
    (hQ2 : quorum (inst := inst.project (I1 ∪ I2)) Q2)
    (hQ1_inter : Q1 ∩ (I1 ∪ I2) ≠ ∅)
    (hQ2_inter : Q2 ∩ (I1 ∪ I2) ≠ ∅) :
    Q1 ∩ Q2 ∩ (I1 ∪ I2) ≠ ∅ := by
  classical
  have hI1_subset : I1 ⊆ I1 ∪ I2 := by
    intro x hx
    exact Or.inl hx
  have hI2_subset : I2 ⊆ I1 ∪ I2 := by
    intro x hx
    exact Or.inr hx
  have hQ1_I1 : quorum (inst := inst.project I1) Q1 :=
    quorum_project_subset (inst := inst) hI1_subset hQ1
  have hQ1_I2 : quorum (inst := inst.project I2) Q1 :=
    quorum_project_subset (inst := inst) hI2_subset hQ1
  have hQ2_I1 : quorum (inst := inst.project I1) Q2 :=
    quorum_project_subset (inst := inst) hI1_subset hQ2
  have hQ2_I2 : quorum (inst := inst.project I2) Q2 :=
    quorum_project_subset (inst := inst) hI2_subset hQ2

  have split_inter : ∀ {Q : Set Node}, Q ∩ (I1 ∪ I2) ≠ ∅ →
      Q ∩ I1 ≠ ∅ ∨ Q ∩ I2 ≠ ∅ := by
    intro Q hQ
    rw [set_ne_empty_iff_exists_mem] at hQ
    rcases hQ with ⟨n, ⟨hnQ, hn_union⟩⟩
    rcases hn_union with hnI1 | hnI2
    · left
      rw [set_ne_empty_iff_exists_mem]
      exact ⟨n, ⟨hnQ, hnI1⟩⟩
    · right
      rw [set_ne_empty_iff_exists_mem]
      exact ⟨n, ⟨hnQ, hnI2⟩⟩

  have promote_I1 : ∀ {Q1 Q2 : Set Node}, Q1 ∩ Q2 ∩ I1 ≠ ∅ →
      Q1 ∩ Q2 ∩ (I1 ∪ I2) ≠ ∅ := by
    intro Q1 Q2 h
    rw [set_ne_empty_iff_exists_mem] at h ⊢
    rcases h with ⟨n, ⟨hnQ12, hnI1⟩⟩
    exact ⟨n, ⟨hnQ12, Or.inl hnI1⟩⟩
  have promote_I2 : ∀ {Q1 Q2 : Set Node}, Q1 ∩ Q2 ∩ I2 ≠ ∅ →
      Q1 ∩ Q2 ∩ (I1 ∪ I2) ≠ ∅ := by
    intro Q1 Q2 h
    rw [set_ne_empty_iff_exists_mem] at h ⊢
    rcases h with ⟨n, ⟨hnQ12, hnI2⟩⟩
    exact ⟨n, ⟨hnQ12, Or.inr hnI2⟩⟩
  have inter_comm : I2 ∩ I1 ≠ ∅ := by
    rw [set_ne_empty_iff_exists_mem] at hinter ⊢
    rcases hinter with ⟨n, ⟨hnI1, hnI2⟩⟩
    exact ⟨n, ⟨hnI2, hnI1⟩⟩
  have hI2_proj_I1 : quorum (inst := inst.project I1) I2 :=
    quorum_after_proj (inst := inst) I2 I1 hI2.q_avail

  rcases split_inter hQ1_inter with hQ1_inter_I1 | hQ1_inter_I2
  · rcases split_inter hQ2_inter with hQ2_inter_I1 | hQ2_inter_I2
    · exact promote_I1 (hI1.q_inter Q1 Q2 hQ1_I1 hQ2_I1 hQ1_inter_I1 hQ2_inter_I1)
    · have hQ1_inter_I2 : Q1 ∩ I2 ≠ ∅ := by
        have h := hI1.q_inter Q1 I2 hQ1_I1 hI2_proj_I1 hQ1_inter_I1 inter_comm
        rw [set_ne_empty_iff_exists_mem] at h ⊢
        rcases h with ⟨n, ⟨⟨hnQ1, hnI2⟩, _hnI1⟩⟩
        exact ⟨n, ⟨hnQ1, hnI2⟩⟩
      exact promote_I2 (hI2.q_inter Q1 Q2 hQ1_I2 hQ2_I2 hQ1_inter_I2 hQ2_inter_I2)
  · rcases split_inter hQ2_inter with hQ2_inter_I1 | hQ2_inter_I2
    · have hQ2_inter_I2 : Q2 ∩ I2 ≠ ∅ := by
        have h := hI1.q_inter Q2 I2 hQ2_I1 hI2_proj_I1 hQ2_inter_I1 inter_comm
        rw [set_ne_empty_iff_exists_mem] at h ⊢
        rcases h with ⟨n, ⟨⟨hnQ2, hnI2⟩, _hnI1⟩⟩
        exact ⟨n, ⟨hnQ2, hnI2⟩⟩
      exact promote_I2 (hI2.q_inter Q1 Q2 hQ1_I2 hQ2_I2 hQ1_inter_I2 hQ2_inter_I2)
    · exact promote_I2 (hI2.q_inter Q1 Q2 hQ1_I2 hQ2_I2 hQ1_inter_I2 hQ2_inter_I2)

/-- The union of two intersecting intact sets is intact. -/
theorem union_intact {I1 I2 : Set Node}
    (hI1 : intact I1)
    (hI2 : intact I2)
    (hinter : I1 ∩ I2 ≠ ∅) :
    intact (I1 ∪ I2) where
  well_behaved := by
    intro n hn
    rcases hn with hnI1 | hnI2
    · exact hI1.well_behaved hnI1
    · exact hI2.well_behaved hnI2
  q_inter := by
    intro Q1 Q2 hQ1 hQ2 hQ1_inter hQ2_inter
    exact union_quorum_intersection hI1 hI2 hinter hQ1 hQ2 hQ1_inter hQ2_inter
  q_avail := union_quorum hI1 hI2

end FBA
