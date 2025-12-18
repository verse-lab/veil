import Std.Data.ExtTreeSet.Basic
import Std.Data.ExtTreeSet.Lemmas
import Std.Data.TreeMap.Lemmas
import Mathlib.Data.FinEnum
import Mathlib.Data.List.Sublists
import Init.Data.Order.Ord
open Std

instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := match x, y with
    | (a, b), (a', b') => compare a a' |>.then (compare b b')

instance [Ord α] [TransOrd α] : Ord (ExtTreeSet α) where
  compare s1 s2 := compare s1.toList s2.toList

instance [Ord α] [DecidableEq α] [TransOrd α] : DecidableEq (ExtTreeSet α) := fun t₁ t₂ =>
  decidable_of_iff (t₁.toList = t₂.toList) ExtTreeSet.toList_inj

inductive State.Label : Type where
      | acceptorVoted
      | acceptorMaxBal
      | sent

structure State (χ : State.Label → Type) where mk ::
      acceptorVoted : χ State.Label.acceptorVoted
      acceptorMaxBal : χ State.Label.acceptorMaxBal
      sent : χ State.Label.sent

class Enumeration (α : Type u) where
  allValues : List α
  complete : ∀ a : α, a ∈ allValues
  [decEq : DecidableEq α]

attribute [instance low] Enumeration.decEq
attribute [grind ←] Enumeration.complete

instance (priority := low) [enum : Enumeration α] [DecidableEq α] : FinEnum α := FinEnum.ofList enum.allValues enum.complete

-- We don't have both directions as instances, as that would create a loop.
def Enumeration.ofFinEnum {α} [FinEnum α] : Enumeration α where
  allValues := FinEnum.toList α
  complete := FinEnum.mem_toList

instance {n : Nat} : Enumeration (Fin n) where
  allValues := List.finRange n
  complete := by simp

instance {α β} [insta : Enumeration α] [instb : Enumeration β] [DecidableEq α] [DecidableEq β] : Enumeration (α × β) where
  allValues := List.product insta.allValues instb.allValues
  complete := by simp only [Prod.forall, List.pair_mem_product]; grind

instance instInhabitedForExtTreeSet [Inhabited α] [Ord α] : Inhabited (ExtTreeSet α) := ⟨ExtTreeSet.empty⟩

instance DecidableEqExtTreeSet [Ord α] [DecidableEq α] [TransOrd α]
  : DecidableEq (ExtTreeSet α) := fun t₁ t₂ =>
  decidable_of_iff (t₁.toList = t₂.toList) ExtTreeSet.toList_inj

instance instEnumerationForExtTreeSet [Enumeration α] [Ord α] [TransOrd α] [LawfulEqOrd α]
  : Enumeration (ExtTreeSet α) where
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


instance LawfulOrdExtTreeSet [Ord α] [TransOrd α] [LawfulEqOrd α]
  : LawfulEqOrd (ExtTreeSet α) where
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


instance TransOrdExtTreeSet [Ord α] [TransOrd α]
  : TransOrd (ExtTreeSet α) where
  eq_swap := by
    intro s1 s2
    dsimp [compare]
    exact OrientedCmp.eq_swap
  isLE_trans := by
    intro s1 s2 s3 h1 h2
    dsimp [compare] at *
    apply TransCmp.isLE_trans h1 h2

abbrev TotalTreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) :=
  { mp : Std.TreeMap α β cmp // ∀ a, a ∈ mp }

instance {cmp : α → α → Ordering} [Enumeration α] [Std.LawfulEqCmp cmp] [Std.TransCmp cmp] [DecidableEq α] [Inhabited β] : Inhabited (TotalTreeMap α β cmp) :=
  ⟨⟨Std.TreeMap.ofList ((Enumeration.allValues).map (fun a => (a, default))) cmp,
    by intro a ; rw [Std.TreeMap.mem_ofList, List.map_map] ; unfold Function.comp ; simp [Enumeration.complete]⟩⟩


abbrev IteratedProd' (ts : List Type) : Type :=
  match ts with
  | [] => Unit
  | [t] => t
  | t :: ts' => t × IteratedProd' ts'

abbrev State.Label.toDomain (ballot : Type) (slot : Type) (value : Type) (acceptor : Type) (quorum : Type)
        (SlotSet : Type) (VotedSet : Type) (DecreeSet : Type) (MsgSet : Type) (__veil_f : State.Label) : List Type :=
      State.Label.casesOn __veil_f [acceptor] [acceptor] []

abbrev State.Label.toCodomain (ballot : Type) (slot : Type) (value : Type) (acceptor : Type) (quorum : Type)
        (SlotSet : Type) (VotedSet : Type) (DecreeSet : Type) (MsgSet : Type) (__veil_f : State.Label) : Type :=
      State.Label.casesOn __veil_f VotedSet ballot MsgSet

abbrev FieldConcreteType (ballot : Type) (slot : Type) (value : Type) (acceptor : Type) (quorum : Type) (SlotSet : Type)
        (VotedSet : Type) (DecreeSet : Type) (MsgSet : Type) [Ord ballot] [Ord slot] [Ord value] [Ord acceptor]
        [Ord quorum] [Ord SlotSet] [Ord VotedSet] [Ord DecreeSet] [Ord MsgSet] (__veil_f : State.Label) : Type :=
      State.Label.casesOn __veil_f
        (TotalTreeMap
          (IteratedProd' <|
            (State.Label.toDomain ballot slot value acceptor quorum SlotSet VotedSet DecreeSet MsgSet)
              State.Label.acceptorVoted)
          ((State.Label.toCodomain ballot slot value acceptor quorum SlotSet VotedSet DecreeSet MsgSet)
            State.Label.acceptorVoted))
        (TotalTreeMap
          (IteratedProd' <|
            (State.Label.toDomain ballot slot value acceptor quorum SlotSet VotedSet DecreeSet MsgSet)
              State.Label.acceptorMaxBal)
          ((State.Label.toCodomain ballot slot value acceptor quorum SlotSet VotedSet DecreeSet MsgSet)
            State.Label.acceptorMaxBal))
        ((State.Label.toCodomain ballot slot value acceptor quorum SlotSet VotedSet DecreeSet MsgSet) State.Label.sent)

section VariousByEquiv
variable {α : Type u} {β : Type v} [Ord α] [Ord β] (equiv : α ≃ β)
  (hmorph : ∀ (a1 a2 : α), compare a1 a2 = compare (equiv a1) (equiv a2))

include hmorph

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

structure Voted (α β γ : Type) where
  bal  : α
  slot : β
  val  : γ
deriving Inhabited, DecidableEq, Repr, Lean.ToJson, Hashable, Ord, Repr

namespace Voted

def votedEquiv : Voted α β γ ≃ (α × β × γ) where
  toFun v := (v.bal, v.slot, v.val)
  invFun := fun (a, b, c) => { bal := a, slot := b, val := c }
  left_inv := by intro v; cases v; rfl
  right_inv := by intro p; rfl


theorem voted_compare_hmorph
  [Ord α] [Ord β] [Ord γ]
  (v1 v2 : Voted α β γ) :
  compare v1 v2 = compare (votedEquiv v1) (votedEquiv v2) := by
  simp [Ord.compare, votedEquiv, instOrdVoted.ord]

instance instTransOrdForVoted
[Ord α] [Ord β] [Ord γ]
[Std.TransOrd α]
[Std.TransOrd β]
[Std.TransOrd γ]
: Std.TransOrd (Voted α β γ) :=
  @Std.TransOrd.by_equiv (α × β × γ) (Voted α β γ) _ _ votedEquiv.symm
    (fun a1 a2 => (voted_compare_hmorph (votedEquiv.symm a1) (votedEquiv.symm a2)).symm)
    inferInstance

instance instLawfulEqOrdForVoted
[Ord α] [Ord β] [Ord γ]
[Std.LawfulEqOrd α]
[Std.LawfulEqOrd β]
[Std.LawfulEqOrd γ]
: Std.LawfulEqOrd (Voted α β γ) :=
  @Std.LawfulEqOrd.by_equiv (α × β × γ) (Voted α β γ) _ _ votedEquiv.symm
    (fun a1 a2 => (voted_compare_hmorph (votedEquiv.symm a1) (votedEquiv.symm a2)).symm)
    inferInstance

instance {α β γ : Type} [FinEnum α] [FinEnum β] [FinEnum γ] : FinEnum (Voted α β γ) :=
  FinEnum.ofEquiv _
    { toFun := fun v => (v.bal, v.slot, v.val)
      invFun := fun (b, s, v) => { bal := b, slot := s, val := v }
      left_inv := by intro v; cases v; simp
      right_inv := by intro x; simp }

end Voted

structure Decree (β γ : Type) where
  slot : β
  val  : γ
deriving Inhabited, DecidableEq, Repr, Lean.ToJson, Hashable, Ord, Repr

namespace Decree

def decreeEquiv : Decree β γ ≃ (β × γ) where
  toFun d := (d.slot, d.val)
  invFun := fun (s, v) => { slot := s, val := v }
  left_inv := by intro d; cases d; rfl
  right_inv := by intro p; rfl

theorem decree_compare_hmorph
  [Ord β] [Ord γ]
  (d1 d2 : Decree β γ) :
  compare d1 d2 = compare (decreeEquiv d1) (decreeEquiv d2) := by
  simp [Ord.compare, decreeEquiv, instOrdDecree.ord]

instance instTransOrdForDecree
[Ord β] [Ord γ]
[Std.TransOrd β]
[Std.TransOrd γ]
: Std.TransOrd (Decree β γ) :=
  @Std.TransOrd.by_equiv (β × γ) (Decree β γ) _ _ decreeEquiv.symm
    (fun a1 a2 => (decree_compare_hmorph (decreeEquiv.symm a1) (decreeEquiv.symm a2)).symm)
    inferInstance

instance instLawfulEqOrdForDecree
[Ord β] [Ord γ]
[Std.LawfulEqOrd β]
[Std.LawfulEqOrd γ]
: Std.LawfulEqOrd (Decree β γ) :=
  @Std.LawfulEqOrd.by_equiv (β × γ) (Decree β γ) _ _ decreeEquiv.symm
    (fun a1 a2 => (decree_compare_hmorph (decreeEquiv.symm a1) (decreeEquiv.symm a2)).symm)
    inferInstance

instance FinEnumDecree {β γ : Type} [FinEnum β] [FinEnum γ] : FinEnum (Decree β γ) :=
  FinEnum.ofEquiv _
    { toFun := fun d => (d.slot, d.val)
      invFun := fun (s, v) => { slot := s, val := v }
      left_inv := by intro d; cases d; simp
      right_inv := by intro x; simp }

end Decree

inductive MsgType where
  | Phase1a
  | Phase1b
  | Phase2a
  | Phase2b
deriving Inhabited, DecidableEq, Ord, Lean.ToJson, Hashable, Repr

instance : FinEnum MsgType :=
  FinEnum.ofList
    [MsgType.Phase1a, MsgType.Phase1b, MsgType.Phase2a, MsgType.Phase2b]
    (by simp; intro x; cases x <;> simp )

instance : Std.TransOrd MsgType where
  eq_swap := by intro a b; cases a <;> cases b <;> decide
  isLE_trans := by intro a b c; cases a <;> cases b <;> cases c <;> decide

instance : Std.LawfulEqOrd MsgType where
  compare_self := by intro a; cases a <;> decide
  eq_of_compare := by intro a b; cases a <;> cases b <;> decide

structure Msg (ac val blt slt vcont dcont : Type) where
  msgType : MsgType
  src : ac
  val : val
  bal : blt
  slot : slt
  decrees : dcont
  voted : vcont
deriving Inhabited, DecidableEq, Lean.ToJson, Hashable, Ord, Repr

namespace Msg

def msgEquiv : Msg ac valT blt slt vcont dcont ≃ (MsgType × ac × valT × blt × slt × dcont × vcont) where
  toFun m := (m.msgType, m.src, m.val, m.bal, m.slot, m.decrees, m.voted)
  invFun := fun (t, s, v, b, sl, d, vo) =>
    { msgType := t, src := s, val := v, bal := b, slot := sl, decrees := d, voted := vo }
  left_inv := by intro m; cases m; rfl
  right_inv := by intro p; rfl

theorem msg_compare_hmorph
  [Ord ac] [Ord valT] [Ord blt] [Ord slt] [Ord vcont] [Ord dcont]
  (m1 m2 : Msg ac valT blt slt vcont dcont) :
  compare m1 m2 = compare (msgEquiv m1) (msgEquiv m2) := by
  simp [Ord.compare, msgEquiv, instOrdMsg.ord]

end Msg

instance {ac val blt slt vcont dcont : Type}
    [FinEnum ac] [FinEnum val] [FinEnum blt]
    [FinEnum slt] [FinEnum vcont] [FinEnum dcont] :
    FinEnum (Msg ac val blt slt vcont dcont) :=
  FinEnum.ofEquiv _
    {
      toFun := fun m => (m.msgType, m.src, m.val, m.bal, m.slot, m.decrees, m.voted)
      invFun := fun (t, s, v, b, sl, d, vo) =>
        { msgType := t, src := s, val := v, bal := b, slot := sl, decrees := d, voted := vo }
      left_inv := by intro m; cases m; simp
      right_inv := by intro x; simp
    }

instance instTransOrdForMsg
[Ord ac] [Ord val] [Ord blt] [Ord slt] [Ord vcont] [Ord dcont]
[Std.TransOrd ac] [Std.TransOrd val] [Std.TransOrd blt] [Std.TransOrd slt] [Std.TransOrd vcont] [Std.TransOrd dcont]
: Std.TransOrd (Msg ac val blt slt vcont dcont) :=
  @Std.TransOrd.by_equiv (MsgType × ac × val × blt × slt × dcont × vcont) (Msg ac val blt slt vcont dcont) _ _ Msg.msgEquiv.symm
    (fun a1 a2 => (Msg.msg_compare_hmorph (Msg.msgEquiv.symm a1) (Msg.msgEquiv.symm a2)).symm)
    inferInstance

instance instLawfulOrdForMsg
[Ord ac] [Ord val] [Ord blt] [Ord slt] [Ord vcont] [Ord dcont]
[Std.LawfulEqOrd ac] [Std.LawfulEqOrd val] [Std.LawfulEqOrd blt] [Std.LawfulEqOrd slt] [Std.LawfulEqOrd vcont] [Std.LawfulEqOrd dcont]
: Std.LawfulEqOrd (Msg ac val blt slt vcont dcont) :=
  @Std.LawfulEqOrd.by_equiv (MsgType × ac × val × blt × slt × dcont × vcont) (Msg ac val blt slt vcont dcont) _ _ Msg.msgEquiv.symm
    (fun a1 a2 => (Msg.msg_compare_hmorph (Msg.msgEquiv.symm a1) (Msg.msgEquiv.symm a2)).symm)
    inferInstance


abbrev ballot := Fin 1
abbrev slot := Fin 1
abbrev value := Fin 1
abbrev acceptor := Fin 1
abbrev quorum := Fin 1
abbrev SlotSet := ExtTreeSet (Fin 1) compare
abbrev VotedSet := ExtTreeSet (Voted (Fin 1) (Fin 1) (Fin 1)) compare
abbrev DecreeSet := ExtTreeSet (Decree (Fin 1) (Fin 1)) compare
abbrev MsgSet := ExtTreeSet (Msg (Fin 1) (Fin 1) (Fin 1) (Fin 1) (ExtTreeSet (Voted (Fin 1) (Fin 1) (Fin 1)) compare) (ExtTreeSet (Decree (Fin 1) (Fin 1)) compare)) compare


#synth Inhabited ballot
#synth Ord ballot
#synth DecidableEq ballot
#synth Enumeration ballot
#synth Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord ballot)))
#synth Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord ballot)))

#synth Inhabited SlotSet
#synth Ord SlotSet
#synth DecidableEq SlotSet
#synth Enumeration SlotSet
#synth Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord SlotSet)))
#synth Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord SlotSet)))

#synth Inhabited VotedSet
#synth Ord VotedSet
#synth DecidableEq VotedSet
#synth Enumeration VotedSet
#synth Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord VotedSet)))
#synth Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord VotedSet)))

#synth Inhabited DecreeSet
#synth Ord DecreeSet
#synth DecidableEq DecreeSet
#synth Enumeration DecreeSet
#synth Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord DecreeSet)))
#synth Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord DecreeSet)))

#synth Inhabited MsgSet
#synth Ord MsgSet
#synth DecidableEq MsgSet
#synth Enumeration MsgSet
#synth Std.LawfulEqCmp (Ord.compare (self := inferInstanceAs (Ord MsgSet)))
#synth Std.TransCmp (Ord.compare (self := inferInstanceAs (Ord MsgSet)))


instance (priority := high + 100) InhabitedState (ballot : Type) (slot : Type) (value : Type) (acceptor : Type) (quorum : Type) (SlotSet : Type)
        (VotedSet : Type) (DecreeSet : Type) (MsgSet : Type) [Inhabited ballot] [Inhabited slot] [Inhabited value]
        [Inhabited acceptor] [Inhabited quorum] [Inhabited SlotSet] [Inhabited VotedSet] [Inhabited DecreeSet]
        [Inhabited MsgSet] [ord_ballot : Ord ballot] [ord_slot : Ord slot] [ord_value : Ord value] [ord_acceptor : Ord acceptor] [ord_quorum : Ord quorum] [ord_SlotSet : Ord SlotSet] [ord_VotedSet : Ord VotedSet]
        [ord_DecreeSet : Ord DecreeSet] [ord_MsgSet : Ord MsgSet] [DecidableEq ballot] [DecidableEq slot] [DecidableEq value] [DecidableEq acceptor]
        [DecidableEq quorum] [DecidableEq SlotSet] [DecidableEq VotedSet] [DecidableEq DecreeSet] [DecidableEq MsgSet]
        [Enumeration ballot] [Enumeration slot] [Enumeration value] [Enumeration acceptor]
        [Enumeration quorum] [Enumeration SlotSet] [Enumeration VotedSet] [Enumeration DecreeSet]
        [Enumeration MsgSet] [Std.LawfulEqCmp (Ord.compare (self := ord_ballot))] [Std.LawfulEqCmp (Ord.compare (self := ord_slot))] [Std.LawfulEqCmp (Ord.compare (self := ord_value))] [Std.LawfulEqCmp (Ord.compare (self := ord_acceptor))] [Std.LawfulEqCmp (Ord.compare (self := ord_quorum))] [Std.LawfulEqCmp (Ord.compare (self := ord_SlotSet))] [Std.LawfulEqCmp (Ord.compare (self := ord_VotedSet))] [Std.LawfulEqCmp (Ord.compare (self := ord_DecreeSet))] [Std.LawfulEqCmp (Ord.compare (self := ord_MsgSet))] [Std.TransCmp (Ord.compare (self := ord_ballot))] [Std.TransCmp (Ord.compare (self := ord_slot))] [Std.TransCmp (Ord.compare (self := ord_value))] [Std.TransCmp (Ord.compare (self := ord_acceptor))] [Std.TransCmp (Ord.compare (self := ord_quorum))] [Std.TransCmp (Ord.compare (self := ord_SlotSet))] [Std.TransCmp (Ord.compare (self := ord_VotedSet))] [Std.TransCmp (Ord.compare (self := ord_DecreeSet))] [Std.TransCmp (Ord.compare (self := ord_MsgSet))] :
        Inhabited (State (FieldConcreteType ballot slot value acceptor quorum SlotSet VotedSet DecreeSet MsgSet)) := by
      constructor; constructor <;> dsimp only [FieldConcreteType] <;> exact Inhabited.default

-- Increase limits for complex instance synthesis
-- set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 500

#synth Inhabited (State (FieldConcreteType ballot slot value acceptor quorum SlotSet VotedSet DecreeSet MsgSet))
