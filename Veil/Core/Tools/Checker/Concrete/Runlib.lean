import Std
import Veil.Frontend.Std
import Veil.Core.Tools.Checker.Concrete.State
import Veil.Frontend.DSL.Infra.GenericInterface

open Lean
/--
`BEq` instances for `Std.TreeMap` and `Std.TreeSet`.

We need `BEq` instance, as we sometimes hope to store them in `HashSet` or `HashMap`,
e.g., debugging, when we hope to store the complete information of a state `σᵣ`.
-/
instance [Ord α] [BEq α]: BEq (Std.TreeSet α) where
  beq s1 s2 :=
    s1.toArray == s2.toArray

instance [Ord α] [BEq α] [BEq β]: BEq (Std.TreeMap α β) where
  beq s1 s2 :=
    s1.toArray == s2.toArray

instance [Ord α] [BEq α] [BEq β]: BEq (Veil.TotalTreeMap α β) where
  beq s1 s2 :=
    s1.val.toArray == s2.val.toArray


/--
`Hashable` instances for `Std.TreeMap` and `Std.TreeSet`

We always need `Hashable` instance. When we run the model checker,
we always store the hashable value of state representation `σᵣ` in `HashSet`.
-/
instance [Hashable α] [BEq α] [Ord α]: Hashable (Std.TreeSet α) where
  hash s := hash s.toArray

instance [Hashable α] [BEq α] [Ord α]: Hashable (Std.TreeSet α) where
  hash := fun s => hash s.toArray

instance [Ord α] [Hashable α] [Hashable β] : Hashable (Std.TreeMap α β) where
  hash s := hash s.toArray

instance [Ord α] [Hashable α] [Hashable β]: Hashable (Veil.TotalTreeMap α β) where
  hash s := hash s.val.toArray


/--
`Ord` instances for `Std.TreeMap` and `Std.TreeSet`

If we want to use `symmetric reduction` in model checking, we need `Ord` instances
to make the states comparable.
 -/
instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := match x, y with
    | (a, b), (a', b') => compare a a' |>.then (compare b b')

instance [Ord α] : Ord (Std.TreeSet α) where
  compare s1 s2 := compare s1.toArray s2.toArray

instance [Ord α] [Ord β] : Ord (Std.TreeMap α β) where
  compare s1 s2 := compare s1.toArray s2.toArray

instance [Ord α] [Ord β]: Ord (Veil.TotalTreeMap α β) where
  compare s1 s2 := compare s1.val.toArray s2.val.toArray


/--
`ToJson` instances
-/
instance [Repr α]: ToJson α where
  toJson := fun a => Json.str (toString (repr a))

instance jsonOfTuple [ToJson α] [ToJson β]: ToJson (α × β) where
  toJson := fun ⟨a, b⟩ => Json.arr #[toJson a, toJson b]

instance jsonOfList [ToJson α]: ToJson (List α) where
  toJson := fun xs => Json.arr (xs.toArray.map toJson)

instance jsonOfTreeSet [Ord α] [ToJson α] : ToJson (Std.TreeSet α) where
  toJson s := Json.arr <| s.toArray.map toJson

instance jsonOfTreeMap [Ord α] [ToJson α] [ToJson β] : ToJson (Std.TreeMap α β) where
  toJson m := Json.arr <| m.toArray.map (fun (k, v) => Json.arr #[toJson k, toJson v])

instance jsonOfTotalTreeMap [Ord α] [ToJson α] [ToJson β] : ToJson (Veil.TotalTreeMap α β) where
  toJson m := Json.arr <| m.val.toArray.map (fun (k, v) => Json.arr #[toJson k, toJson v])

instance jsonOfTrace {σₛ κ : Type} [ToJson σₛ] [ToJson κ] : ToJson (Trace σₛ κ) where
  toJson := fun tr =>
    let states : Array Json :=
      #[ Json.mkObj
        [ ("index", toJson 0),
          ("fields", toJson tr.start),
          ("action", "after_init") ]] ++
      (tr.steps.toArray.mapIdx (fun i st =>
        let idx := i + 1
        Json.mkObj
        [ ("index", toJson idx),
          ("fields", toJson st.next),
          ("action", toJson st.label)]))
    Json.arr states



instance (n : Nat): TotalOrderWithZero (Fin n.succ) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega
  zero := ⟨0, by simp⟩
  zero_le := by simp


instance (n : Nat) : DecidableRel (TotalOrderWithZero.le (t := Fin n.succ)) := by
  dsimp [TotalOrderWithZero.le]
  infer_instance_for_iterated_prod


instance (n : Nat): TotalOrderWithMinimum (Fin n.succ) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega
  lt := fun x y => x.val < y.val
  le_lt := by intros; dsimp [TotalOrderWithMinimum.lt, TotalOrderWithMinimum.le]; omega
  next := fun x y => x.val + 1 = y.val
  next_def := by
    intros x y
    dsimp [TotalOrderWithMinimum.next, TotalOrderWithMinimum.lt, TotalOrderWithMinimum.le]
    apply Iff.intro
    · -- Forward direction: x.val + 1 = y.val → (x.val < y.val ∧ ∀ z, x.val < z.val → y.val ≤ z.val)
      intro h
      constructor
      · -- Prove x.val < y.val
        omega
      · -- Prove ∀ z, x.val < z.val → y.val ≤ z.val
        intro z hz
        omega
    · -- Backward direction: (x.val < y.val ∧ ∀ z, x.val < z.val → y.val ≤ z.val) → x.val + 1 = y.val
      intro ⟨hlt, hmin⟩
      have h1 : x.val < x.val + 1 := by omega
      have h2 : y.val ≤ x.val + 1 := hmin ⟨x.val + 1, by omega⟩ h1
      omega
  zero := ⟨0, by simp⟩
  zero_lt := by simp ;



instance (n : Nat) : DecidableRel (TotalOrderWithMinimum.le (t := Fin n.succ)) := by
  dsimp [TotalOrderWithMinimum.le]
  infer_instance_for_iterated_prod

instance (n : Nat) : DecidableRel (TotalOrderWithMinimum.lt (t := Fin n.succ)) := by
  dsimp [TotalOrderWithMinimum.lt]
  infer_instance_for_iterated_prod

instance (n : Nat) : DecidableRel (TotalOrderWithMinimum.next (t := Fin n.succ)) := by
  dsimp [TotalOrderWithMinimum.next]
  infer_instance_for_iterated_prod


-- instance [Ord α]
--   : Ord (FieldConcreteType α states State.Label.locked) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord α]
--   : Ord (FieldConcreteType α states State.Label.wait_queue_wakers) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord α]
--   : Ord (FieldConcreteType α states State.Label.locked) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord α]
--   : Ord (FieldConcreteType α states State.Label.has_woken) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord α]
--   : Ord (FieldConcreteType α states State.Label.pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord α]
--   : Ord (FieldConcreteType α states State.Label.stack_pc) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord α]
--   : Ord (FieldConcreteType α states State.Label.stack_waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance [Ord α]
--   : Ord (FieldConcreteType α states State.Label.waker) := by
--   dsimp only [FieldConcreteType, State.Label.toCodomain, State.Label.toDomain, Veil.IteratedProd'];
--   infer_instance_for_iterated_prod

-- instance: Ord StateConcrete where
--   compare a b :=
--     compare a.locked b.locked |>.then
--     (compare a.wait_queue_wakers b.wait_queue_wakers) |>.then
--     (compare a.has_woken b.has_woken) |>.then
--     (compare a.pc b.pc) |>.then
--     (compare a.stack_pc b.stack_pc) |>.then
--     (compare a.stack_waker b.stack_waker) |>.then
--     (compare a.waker b.waker)
