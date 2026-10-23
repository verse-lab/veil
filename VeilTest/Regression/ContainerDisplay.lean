module

public import Veil
public meta import Veil

open Lean Veil

/-! The concrete containers are structures over their storage. They keep the storage's equality,
hash and ordering, and display their logical contents (entries, members, multiplicities, FIFO
order) rather than the storage. -/
namespace ContainerDisplayRegression

-- Wrapping must preserve the storage's equality, hash, and ordering.
example [FinEncodable α] [Hashable β] (m : ArrayAsFinmap α β) : hash m = hash m.val := rfl
example [FinEncodable α] (s : ArrayAsFinset α) : hash s = hash s.val := rfl
example [FinEncodable α] [FinEncodable β] (m : BitVecAsFinmap α β) : hash m = hash m.bits := rfl
example [Ord α] [Hashable α] (s : OrdList α) : hash s = hash s.val := rfl
example [Ord α] [Hashable α] (s : OrdArray α) : hash s = hash s.val := rfl
example [Ord α] [Std.TransOrd α] [Hashable α] (s : TMapMultiset α) : hash s = hash s.val := rfl
example [Ord α] (s t : OrdList α) : compare s t = compare s.val t.val := rfl
example [Ord α] (s t : OrdArray α) : compare s t = compare s.val t.val := rfl
example [Ord α] [Std.TransOrd α] (s t : TMapMultiset α) :
    compare s t = compare s.val.toList t.val.toList := rfl

-- Keep phantom parameters unconstrained and BEq available without LawfulBEq.
example [FinEncodable α] [BEq β] : BEq (ArrayAsFinmap α β) := inferInstance
example [FinEncodable α] [DecidableEq β] : DecidableEq (ArrayAsFinmap α β) := inferInstance
example [FinEncodable α] [BEq β] [ReflBEq β] : ReflBEq (ArrayAsFinmap α β) := inferInstance
example [FinEncodable α] [BEq β] [LawfulBEq β] : LawfulBEq (ArrayAsFinmap α β) := inferInstance
example [Ord α] [BEq α] : BEq (OrdList α) := inferInstance
example [Ord α] [BEq α] : BEq (OrdArray α) := inferInstance

example : LawfulBEq (ArrayAsFinmap (Fin 3) Nat) := inferInstance
example : LawfulBEq (ArrayAsFinset (Fin 3)) := inferInstance
example : LawfulBEq (BitVecAsFinmap (Fin 3) (Fin 3)) := inferInstance
example : LawfulBEq (OrdList (Fin 3)) := inferInstance
example : LawfulBEq (OrdArray (Fin 3)) := inferInstance
example : LawfulBEq (TMapMultiset (Fin 3)) := inferInstance
example : Std.TransOrd (OrdList (Fin 3)) := inferInstance
example : Std.LawfulEqOrd (OrdArray (Fin 3)) := inferInstance
example : Std.LawfulEqOrd (TMapMultiset (Fin 3)) := inferInstance
example : DecidableEq (ArrayAsFinmap (Fin 3) Nat) := inferInstance
example : FinEncodable (BitVecAsFinmap (Fin 3) (Fin 3)) := inferInstance

/-! Array and bit-vector field representations display as the functions and sets they represent. -/
run_cmd do
  let m : ArrayAsFinmap (Fin 3) (Option Nat) := FinmapLike.insert 1 (some 7) default
  unless toJson m == json% [[0, null], [1, 7], [2, null]] &&
      reprStr m == "{0 ↦ none, 1 ↦ some 7, 2 ↦ none}" do
    throwError "array map must show its entries, keyed by the domain"
  let s : ArrayAsFinset (Fin 3) := FinmapLike.insert 2 true default
  unless toJson s == json% [2] && reprStr s == "{2}" do
    throwError "array set must show its members, not its Boolean storage"
  unless toJson (default : ArrayAsFinmap (Fin 0) Nat) == json% [] &&
      toJson (default : ArrayAsFinset (Fin 0)) == json% [] do
    throwError "empty domains must give empty containers"
  -- Tuple keys follow the finite-function convention, so both representations look the same.
  let tuples : ArrayAsFinmap (Fin 1 × Fin 1) Nat := FinmapLike.insert (0, 0) 7 default
  unless toJson tuples == json% [[0, 0, 7]] &&
      toJson tuples == toJson (fun (_ : Fin 1 × Fin 1) => (7 : Nat)) do
    throwError "an array map must display as the function it represents"
  let b : BitVecAsFinmap (Fin 3) (Fin 3) := FinmapLike.insert 1 2 default
  unless toJson b == json% [[0, 0], [1, 2], [2, 0]] && reprStr b == "{0 ↦ 0, 1 ↦ 2, 2 ↦ 0}" do
    throwError "bit map must show its decoded entries, not its bits"
  -- All raw bit patterns remain encodable, including unused codomain patterns.
  let enc := FinEncodable.equiv (α := BitVecAsFinmap (Fin 3) (Fin 3))
  for i in List.finRange 64 do
    let m := enc.symm i
    unless enc m == i && hash m == hash m.bits do
      throwError "bit map encoding or hash changed"
    for k in List.finRange 3 do
      for v in List.finRange 3 do
        let updated := FinmapLike.insert k v m
        for k' in List.finRange 3 do
          unless FinmapLike.get updated k' == (if k == k' then v else FinmapLike.get m k') do
            throwError "bit map update changed another key"

/-! Sorted sets serialize their elements with the elements' own `ToJson`. -/
run_cmd do
  unless toJson (OrdList.ofList [2, 0]) == json% [0, 2] &&
      toJson (OrdArray.ofList [2, 0]) == json% [0, 2] do
    throwError "sorted sets must serialize numbers as numbers"
  unless toJson (OrdList.ofList ["b", "a"]) == json% ["a", "b"] &&
      toJson (OrdArray.ofList ["b", "a"]) == json% ["a", "b"] do
    throwError "sorted sets must serialize strings as strings, not as their `Repr`"
  unless reprStr (OrdList.ofList [2, 0]) == "[0, 2]" && reprStr (OrdArray.ofList [2, 0]) == "[0, 2]" do
    throwError "sorted set Repr changed"
  let subsets : List (List Nat) := [[], [0], [1], [0, 1]]
  unless toJson (Enumeration.allValues (α := OrdList (Fin 2))) == toJson subsets &&
      toJson (Enumeration.allValues (α := OrdArray (Fin 2))) == toJson subsets do
    throwError "sorted set enumeration changed"

/-! A multiset shows each distinct element with its actual multiplicity; the storage keeps the
multiplicity minus one. -/
run_cmd do
  let bag : TMapMultiset Nat := TMultiset.insert 2 (TMultiset.insert 2 (TMultiset.insert 1 TMultiset.empty))
  unless toJson bag == json% [[1, 1], [2, 2]] && reprStr bag == "{1 × 1, 2 × 2}" do
    throwError "multiset display must show actual multiplicities"
  unless decide (2 ∈ bag) && !decide (3 ∈ bag) do
    throwError "multiset membership changed"
  let bag := TMultiset.remove 2 bag
  unless TMultiset.count 2 bag == 1 && TMultiset.size bag == 2 &&
      toJson bag == json% [[1, 1], [2, 1]] do
    throwError "multiset removal changed its semantics"
  let empty : TMapMultiset Nat := TMultiset.empty
  unless toJson empty == json% [] && reprStr empty == "{}" do
    throwError "empty multiset must display as empty"
  let pairs : TMapMultiset (Nat × Nat) :=
    TMultiset.insert (1, 2) (TMultiset.insert (1, 2) TMultiset.empty)
  unless toJson pairs == json% [[[1, 2], 2]] && reprStr pairs == "{(1, 2) × 2}" do
    throwError "tuple multiset elements must stay whole"

/-! A queue shows its FIFO contents, independently of how they are split between front and back. -/
run_cmd do
  let q := fQueue.empty.enqueue (1 : Nat) |>.enqueue 2 |>.enqueue 3
  let (_, rest) := q.dequeueD
  let q' := rest.enqueue 4
  unless toJson q' == toJson ([2, 3, 4] : List Nat) && reprStr q' == "[2, 3, 4]" do
    throwError "queue display must preserve FIFO order"
  unless toJson q' == toJson (fQueue.ofList [2, 3, 4]) do
    throwError "queue display must be independent of its front/back layout"
  unless toJson (fQueue.empty : fQueue Nat) == Json.arr #[] do
    throwError "empty queue must display as an empty sequence"

-- The generator rejects ambiguous storage rather than silently dropping data.
structure TwoPayloads where
  first : Nat
  second : Nat

/-- error: Expected a structure with exactly one non-proof field -/
#guard_msgs in
veil_derive_wrapper_instances TwoPayloads

end ContainerDisplayRegression

/-! The state's `ToJson` uses the field representations' instances. -/
veil module DirectContainerJson
type key
function values : key → Option Nat
relation selected : key → Bool
veil_set_field_representation function Veil.ArrayAsFinmap
veil_set_field_representation relation Veil.ArrayAsFinset
#gen_state

run_cmd do
  let s : State (FieldConcreteType (Fin 2)) := {
    values := FinmapLike.insert 1 (some 7) (default : ArrayAsFinmap (Fin 2) (Option Nat))
    selected := FinmapLike.insert 1 true (default : ArrayAsFinset (Fin 2)) }
  let json := toJson s
  unless json.getObjValD "values" == json% [[0, null], [1, 7]] &&
      json.getObjValD "selected" == json% [1] do
    throwError "state JSON must use the field representations' instances: {json}"

end DirectContainerJson
