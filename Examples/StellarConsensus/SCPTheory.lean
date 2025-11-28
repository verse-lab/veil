-- skip eval
import Mathlib.Data.Set.Basic

-- adapted from [FBA.thy](https://github.com/stellar/scp-proofs/blob/ac41c6353fae870c47c0e7ee558da98c03a7d041/FBA.thy)

/-
  NOTE: For now we do not prove SCP's liveness property in Veil, so we
  only adapt the definitions that are sufficient for justifying the
  assumptions in the current Veil model of SCP.
-/

theorem Set.ne_empty_iff_exists_mem {α : Type u} {s : Set α} : s ≠ ∅ ↔ ∃ a, a ∈ s := by
  rw [← Set.nonempty_iff_ne_empty] ; aesop

namespace FBA

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
      rw [Set.ne_empty_iff_exists_mem] at h ⊢ ; aesop }

variable [inst : System Node]
open System

/-- A quorum is a set whose well-behaved members have at least one slice
    included in the set. -/
def quorum (Q : Set Node) : Prop := ∀ p ∈ Q ∩ W, ∃ Sl ∈ slices p, Sl ⊆ Q

-- `System.project` allows more quorums
theorem quorum_after_proj (Q S : Set Node) : quorum (inst := inst) Q → quorum (inst := inst.project S) Q := by
  rcases inst with ⟨W, slices, slices_ne⟩
  unfold quorum System.project FBA.project ; simp
  intro hq p h1 h2 ; specialize hq _ h1 h2 ; rcases hq with ⟨Sl, hq1, hq2⟩
  exists Sl ; apply And.intro ; assumption
  rw [Set.subset_def] at hq2 ⊢ ; simp ; aesop

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

theorem intact_implies_intertwined : ∀ I, intact (inst := inst) I → intertwined I := by
  intro I h ; cases h ; assumption

theorem intertwined_node_is_well_behaved : ∀ n S, intertwined (inst := inst) S → n ∈ S → n ∈ W := by
  intro n S ⟨h, _⟩ ; aesop

theorem intact_node_is_well_behaved : ∀ n I, intact (inst := inst) I → n ∈ I → n ∈ W := by
  intro n S h ; apply intertwined_node_is_well_behaved ; apply intact_implies_intertwined _ h

theorem slice_blocks_ne : ∀ n S I, intact (inst := inst) I → n ∈ I → blocks_slices S n →
    S ∩ I ≠ ∅ := by
  intro n S I hI hin hblock
  unfold blocks_slices at hblock
  have h := hI.q_avail ; unfold quorum at h
  simp at h ; specialize h _ hin (intact_node_is_well_behaved _ _ hI hin)
  rcases h with ⟨Sl, hSl, h⟩ ; specialize hblock _ hSl
  rw [Set.ne_empty_iff_exists_mem] at hblock ⊢ ; simp at hblock ⊢
  aesop

end FBA
