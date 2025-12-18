/-
  Minimal test case demonstrating an instance synthesis bug.

  The issue: `#synth Inhabited (State (FieldConcreteType ballot MsgSet))` fails,
  but `def xx : Inhabited (...) := by apply InhabitedState` succeeds with the exact same type.

  This shows that Lean can synthesize the instance manually but fails to find it automatically.
-/

import Std.Data.ExtTreeSet.Basic
import Std.Data.ExtTreeSet.Lemmas
import Std.Data.TreeMap.Lemmas
import Mathlib.Data.FinEnum
import Mathlib.Data.List.Sublists
import Init.Data.Order.Ord
open Std

-- ============================================================================
-- Basic Type Class Instances
-- ============================================================================

instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := match x, y with
    | (a, b), (a', b') => compare a a' |>.then (compare b b')

instance [Ord α] [TransOrd α] : Ord (ExtTreeSet α) where
  compare s1 s2 := compare s1.toList s2.toList

instance [Ord α] [DecidableEq α] [TransOrd α] : DecidableEq (ExtTreeSet α) := fun t₁ t₂ =>
  decidable_of_iff (t₁.toList = t₂.toList) ExtTreeSet.toList_inj

-- ============================================================================
-- Enumeration Type Class
-- ============================================================================

class Enumeration (α : Type u) where
  allValues : List α
  complete : ∀ a : α, a ∈ allValues
  [decEq : DecidableEq α]

attribute [instance low] Enumeration.decEq
attribute [grind ←] Enumeration.complete

instance (priority := low) [enum : Enumeration α] [DecidableEq α] : FinEnum α :=
  FinEnum.ofList enum.allValues enum.complete

def Enumeration.ofFinEnum {α} [FinEnum α] : Enumeration α where
  allValues := FinEnum.toList α
  complete := FinEnum.mem_toList

instance {n : Nat} : Enumeration (Fin n) where
  allValues := List.finRange n
  complete := by simp

instance {α β} [insta : Enumeration α] [instb : Enumeration β] [DecidableEq α] [DecidableEq β] :
    Enumeration (α × β) where
  allValues := List.product insta.allValues instb.allValues
  complete := by simp only [Prod.forall, List.pair_mem_product]; grind

-- ============================================================================
-- ExtTreeSet Instances
-- ============================================================================

instance instInhabitedForExtTreeSet [Inhabited α] [Ord α] : Inhabited (ExtTreeSet α) :=
  ⟨ExtTreeSet.empty⟩

instance DecidableEqExtTreeSet [Ord α] [DecidableEq α] [TransOrd α] : DecidableEq (ExtTreeSet α) :=
  fun t₁ t₂ => decidable_of_iff (t₁.toList = t₂.toList) ExtTreeSet.toList_inj

instance instEnumerationForExtTreeSet [Enumeration α] [Ord α] [TransOrd α] [LawfulEqOrd α] :
    Enumeration (ExtTreeSet α) where
  allValues := Enumeration.allValues (α := α).sublists.map (ExtTreeSet.ofList ·)
  complete := by
    intro s
    rw [List.mem_map]
    let l := Enumeration.allValues (α := α).filter (· ∈ s)
    exists l
    constructor
    · rw [List.mem_sublists]
      exact List.filter_sublist
    · apply Std.ExtTreeSet.ext_mem
      intro k
      rw [Std.ExtTreeSet.mem_ofList]
      grind

instance [Ord α] [FinEnum α] [TransOrd α] [LawfulEqOrd α] : Enumeration (ExtTreeSet α) :=
  @instEnumerationForExtTreeSet (α := α) (Enumeration.ofFinEnum (α := α)) _ _ _

instance LawfulOrdExtTreeSet [Ord α] [TransOrd α] [LawfulEqOrd α] : LawfulEqOrd (ExtTreeSet α) where
  compare_self := by
    intro s
    dsimp [compare]
    exact ReflCmp.compare_self
  eq_of_compare := by
    intro s1 s2 h
    dsimp [compare] at h
    apply Std.ExtTreeSet.ext_mem
    intro a
    have : s1.toList = s2.toList := LawfulEqCmp.eq_of_compare h
    rw [← Std.ExtTreeSet.mem_toList, this, Std.ExtTreeSet.mem_toList]

instance TransOrdExtTreeSet [Ord α] [TransOrd α] : TransOrd (ExtTreeSet α) where
  eq_swap := by
    intro s1 s2
    dsimp [compare]
    exact OrientedCmp.eq_swap
  isLE_trans := by
    intro s1 s2 s3 h1 h2
    dsimp [compare] at *
    apply TransCmp.isLE_trans h1 h2

-- ============================================================================
-- Helper Utilities
-- ============================================================================

/-- A map from all values of an enumerable type α to values of type β -/
abbrev TotalTreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) :=
  { mp : Std.TreeMap α β cmp // ∀ a, a ∈ mp }

instance {cmp : α → α → Ordering} [Enumeration α] [Std.LawfulEqCmp cmp] [Std.TransCmp cmp]
    [DecidableEq α] [Inhabited β] : Inhabited (TotalTreeMap α β cmp) :=
  ⟨⟨Std.TreeMap.ofList ((Enumeration.allValues).map (fun a => (a, default))) cmp,
    by intro a ; rw [Std.TreeMap.mem_ofList, List.map_map] ; unfold Function.comp ;
       simp [Enumeration.complete]⟩⟩

/-- Iterated product of a list of types -/
abbrev IteratedProd' (ts : List Type) : Type :=
  match ts with
  | [] => Unit
  | [t] => t
  | t :: ts' => t × IteratedProd' ts'

section VariousByEquiv
variable {α : Type u} {β : Type v} [Ord α] [Ord β] (equiv : α ≃ β)
  (hmorph : ∀ (a1 a2 : α), compare a1 a2 = compare (equiv a1) (equiv a2))

include hmorph

/-- Helper for transferring TransOrd instances via equivalence -/
def Std.TransOrd.by_equiv [inst : Std.TransOrd α] : Std.TransOrd β where
  eq_swap := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.eq_swap
  isLE_trans := by
    intro b1 b2 b3
    rw [← equiv.right_inv b1, ← equiv.right_inv b2, ← equiv.right_inv b3] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    apply inst.isLE_trans

def Std.LawfulEqOrd.by_equiv [inst : Std.LawfulEqOrd α] : Std.LawfulEqOrd β where
  compare_self := by
    intro b ; specialize hmorph (equiv.symm b) (equiv.symm b) ; grind
  eq_of_compare := by
    intro b1 b2
    rw [← equiv.right_inv b1, ← equiv.right_inv b2] ; dsimp [Equiv.coe_fn_mk]
    repeat rw [← hmorph]
    simp

end VariousByEquiv

-- ============================================================================
-- Domain Types (simplified versions of structures from the original codebase)
-- ============================================================================

/-- Simplified Voted structure with a single field -/
structure Voted (α : Type) where
  val  : α
deriving Inhabited, DecidableEq, Repr, Lean.ToJson, Hashable, Ord, Repr

namespace Voted

def votedEquiv : Voted α ≃ α where
  toFun v := v.val
  invFun := fun a => { val := a }
  left_inv := by intro v; cases v; rfl
  right_inv := by intro p; rfl

theorem voted_compare_hmorph [Ord α] (v1 v2 : Voted α) :
  compare v1 v2 = compare (votedEquiv v1) (votedEquiv v2) := by
  simp [Ord.compare, votedEquiv, instOrdVoted.ord]

instance instTransOrdForVoted [Ord α] [Std.TransOrd α] : Std.TransOrd (Voted α) :=
  @Std.TransOrd.by_equiv α (Voted α) _ _ votedEquiv.symm
    (fun a1 a2 => (voted_compare_hmorph (votedEquiv.symm a1) (votedEquiv.symm a2)).symm)
    inferInstance

instance instLawfulEqOrdForVoted [Ord α] [Std.LawfulEqOrd α] : Std.LawfulEqOrd (Voted α) :=
  @Std.LawfulEqOrd.by_equiv α (Voted α) _ _ votedEquiv.symm
    (fun a1 a2 => (voted_compare_hmorph (votedEquiv.symm a1) (votedEquiv.symm a2)).symm)
    inferInstance

instance {α : Type} [FinEnum α] : FinEnum (Voted α) :=
  FinEnum.ofEquiv _
    { toFun := fun v => v.val
      invFun := fun a => { val := a }
      left_inv := by intro v; cases v; simp
      right_inv := by intro x; simp }

end Voted

/-- Message structure with multiple type parameters -/
structure Msg (ac val slt vcont : Type) where
  -- !!! Removing any of the below makes the problem go away !!!
  src : ac
  val : val
  slot : slt
  -- !!! Removing any of the above makes the problem go away !!!
  voted : vcont
deriving Inhabited, DecidableEq, Lean.ToJson, Hashable, Ord, Repr

namespace Msg

def msgEquiv : Msg ac valT slt vcont ≃ (ac × valT × slt × vcont) where
  toFun m := (m.src, m.val, m.slot, m.voted)
  invFun := fun (s, v, sl, vo) =>
    { src := s, val := v, slot := sl, voted := vo }
  left_inv := by intro m; cases m; rfl
  right_inv := by intro p; rfl

theorem msg_compare_hmorph [Ord ac] [Ord valT] [Ord slt] [Ord vcont]
    (m1 m2 : Msg ac valT slt vcont) :
  compare m1 m2 = compare (msgEquiv m1) (msgEquiv m2) := by
  simp [Ord.compare, msgEquiv, instOrdMsg.ord]

end Msg

instance {ac val slt vcont : Type}
    [FinEnum ac] [FinEnum val]
    [FinEnum slt] [FinEnum vcont] :
    FinEnum (Msg ac val slt vcont) :=
  FinEnum.ofEquiv _
    {
      toFun := fun m => (m.src, m.val, m.slot, m.voted)
      invFun := fun (s, v, sl, vo) =>
        { src := s, val := v, slot := sl, voted := vo }
      left_inv := by intro m; cases m; simp
      right_inv := by intro x; simp
    }

instance instTransOrdForMsg
    [Ord ac] [Ord val] [Ord slt] [Ord vcont]
    [Std.TransOrd ac] [Std.TransOrd val] [Std.TransOrd slt] [Std.TransOrd vcont] :
    Std.TransOrd (Msg ac val slt vcont) :=
  @Std.TransOrd.by_equiv (ac × val × slt × vcont) (Msg ac val slt vcont) _ _
    Msg.msgEquiv.symm
    (fun a1 a2 => (Msg.msg_compare_hmorph (Msg.msgEquiv.symm a1) (Msg.msgEquiv.symm a2)).symm)
    inferInstance

instance instLawfulOrdForMsg
    [Ord ac] [Ord val] [Ord slt] [Ord vcont]
    [Std.LawfulEqOrd ac] [Std.LawfulEqOrd val] [Std.LawfulEqOrd slt]
    [Std.LawfulEqOrd vcont] :
    Std.LawfulEqOrd (Msg ac val slt vcont) :=
  @Std.LawfulEqOrd.by_equiv (ac × val × slt × vcont) (Msg ac val slt vcont) _ _
    Msg.msgEquiv.symm
    (fun a1 a2 => (Msg.msg_compare_hmorph (Msg.msgEquiv.symm a1) (Msg.msgEquiv.symm a2)).symm)
    inferInstance

-- ============================================================================
-- State Structure and Field Types
-- ============================================================================

/-- State field labels -/
inductive State.Label : Type where
  | acceptorVoted
  | acceptorMaxBal
  | sent

/-- State structure parameterized by a function mapping labels to types -/
structure State (χ : State.Label → Type) where mk ::
  acceptorVoted : χ State.Label.acceptorVoted
  acceptorMaxBal : χ State.Label.acceptorMaxBal
  sent : χ State.Label.sent

/-- Domain of each state field (types that are used as map keys) -/
abbrev State.Label.toDomain (ballot : Type) (__veil_f : State.Label) : List Type :=
  State.Label.casesOn __veil_f [ballot] [ballot] []

/-- Codomain of each state field (types that are stored in the map values) -/
abbrev State.Label.toCodomain (ballot : Type) (MsgSet : Type) (__veil_f : State.Label) : Type :=
  State.Label.casesOn __veil_f MsgSet ballot MsgSet

/-- Concrete type of each state field -/
abbrev FieldConcreteType (ballot : Type) (MsgSet : Type)
    [Ord ballot] [Ord MsgSet] (__veil_f : State.Label) : Type :=
  State.Label.casesOn __veil_f
    (TotalTreeMap
      (IteratedProd' <| (State.Label.toDomain ballot) State.Label.acceptorVoted)
      ((State.Label.toCodomain ballot MsgSet) State.Label.acceptorVoted))
    (TotalTreeMap
      (IteratedProd' <| (State.Label.toDomain ballot) State.Label.acceptorMaxBal)
      ((State.Label.toCodomain ballot MsgSet) State.Label.acceptorMaxBal))
    ((State.Label.toCodomain ballot MsgSet) State.Label.sent)

-- ============================================================================
-- Concrete Type Instantiations
-- ============================================================================

abbrev ballot := Fin 1
abbrev MsgSet := ExtTreeSet (Msg (Fin 1) (Fin 1) (Fin 1)
              -- It's somehow related to having nested `ExtTreeSet`s
              -- If this is replaced with `(Fin 1)`, the instance synthesizes.
              (ExtTreeSet (Voted (Fin 1)) compare)
  ) compare

/- Verify all prerequisite instances are synthesizable -/
#synth Inhabited ballot
#synth Ord ballot
#synth DecidableEq ballot
#synth Enumeration ballot
#synth Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord ballot)))
#synth Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord ballot)))

#synth Inhabited MsgSet
#synth Ord MsgSet
#synth DecidableEq MsgSet
#synth Enumeration MsgSet
#synth Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord MsgSet)))
#synth Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord MsgSet)))

-- ============================================================================
-- The Bug: Instance Synthesis Failure
-- ============================================================================

/--
  This instance should be found automatically by `#synth`, but it isn't.
  It requires all the necessary instances that we've verified above.
-/
instance (priority := high) InhabitedState (ballot : Type) (MsgSet : Type)
    [Inhabited ballot] [Inhabited MsgSet]
    [ord_ballot : Ord ballot] [ord_MsgSet : Ord MsgSet]
    [DecidableEq ballot] [DecidableEq MsgSet]
    [Enumeration ballot] [Enumeration MsgSet]
    [Std.LawfulEqCmp (Ord.compare (self := ord_ballot))]
    [Std.LawfulEqCmp (Ord.compare (self := ord_MsgSet))]
    [Std.TransCmp (Ord.compare (self := ord_ballot))]
    [Std.TransCmp (Ord.compare (self := ord_MsgSet))] :
    Inhabited (State (FieldConcreteType ballot MsgSet)) := by
  constructor; constructor <;> dsimp only [FieldConcreteType] <;> exact Inhabited.default

set_option trace.Meta.synthInstance true

-- This FAILS to synthesize, even though the instance exists It seems there's some
-- kind of repeated "propagating" that causes the instance to not be found. It
-- seems to bottom out here:
-- [resume] propagating TransOrd
--       (ExtTreeSet (Msg (Fin 1) (Fin 1) (Fin 1) (Fin 1) (ExtTreeSet (Voted (Fin 1)) compare))
--         compare) to subgoal TransCmp compare of Inhabited (State (FieldConcreteType ballot MsgSet)) ▼
--   [] size: 128
--   [answer] ❌️ Inhabited (State (FieldConcreteType ballot MsgSet))
--       (size: 128 ≥ 128)

#synth Inhabited (State (FieldConcreteType ballot MsgSet))

-- But this SUCCEEDS by manually applying the instance
def xx : Inhabited (State (FieldConcreteType ballot MsgSet)) := by apply InhabitedState
