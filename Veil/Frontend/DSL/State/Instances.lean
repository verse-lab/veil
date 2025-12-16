import Std
import Veil.Frontend.Std
import Veil.Frontend.DSL.State

namespace Veil
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
  hash s := s.foldl (fun r a => mixHash r (hash a)) 7

instance [Ord α] [Hashable α] [Hashable β] : Hashable (Std.TreeMap α β) where
  hash s := s.foldl (fun r a b => mixHash r (mixHash (hash a) (hash b))) 7

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

end Veil
