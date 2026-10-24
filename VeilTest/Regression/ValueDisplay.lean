module

public import Veil
public meta import Veil

open Lean Veil

/-! The concrete containers are structures over their storage. They keep the storage's equality,
hash and ordering, and display their logical contents (entries, members, multiplicities, FIFO
order) rather than the storage. In JSON, sets, maps and multisets are tagged
(`Veil.ValueDisplay`), and the text of traces and counterexamples renders the tags in set
notation. -/
namespace ValueDisplayRegression

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

-- A subtype displays as its value, e.g. a quorum as its set.
example [ToJson α] {P : α → Prop} (s : Subtype P) : toJson s = toJson s.val := rfl

/-! Array and bit-vector field representations display as the functions and sets they represent. -/
run_cmd do
  let m : ArrayAsFinmap (Fin 3) (Option Nat) := FinmapLike.insert 1 (some 7) default
  unless toJson m == json% {"$veil": "map", entries: [{key: 0, value: null}, {key: 1, value: 7},
        {key: 2, value: null}]} &&
      reprStr m == "{0 ↦ none, 1 ↦ some 7, 2 ↦ none}" do
    throwError "array map must show its entries, keyed by the domain"
  let s : ArrayAsFinset (Fin 3) := FinmapLike.insert 2 true default
  unless toJson s == json% {"$veil": "set", elements: [2]} && reprStr s == "{2}" do
    throwError "array set must show its members, not its Boolean storage"
  unless toJson (default : ArrayAsFinmap (Fin 0) Nat) == json% {"$veil": "map", entries: []} &&
      toJson (default : ArrayAsFinset (Fin 0)) == json% {"$veil": "set", elements: []} do
    throwError "empty domains must give empty containers"
  -- Tuple keys stay whole, and both representations of a function look the same.
  let tuples : ArrayAsFinmap (Fin 1 × Fin 1) Nat := FinmapLike.insert (0, 0) 7 default
  unless toJson tuples == json% {"$veil": "map", entries: [{key: [0, 0], value: 7}]} &&
      toJson tuples == toJson (fun (_ : Fin 1 × Fin 1) => (7 : Nat)) &&
      reprStr tuples == reprStr (fun (_ : Fin 1 × Fin 1) => (7 : Nat)) do
    throwError "an array map must display as the function it represents"
  let b : BitVecAsFinmap (Fin 3) (Fin 3) := FinmapLike.insert 1 2 default
  unless toJson b == json% {"$veil": "map", entries: [{key: 0, value: 0}, {key: 1, value: 2},
        {key: 2, value: 0}]} && reprStr b == "{0 ↦ 0, 1 ↦ 2, 2 ↦ 0}" do
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

/-! Sets and maps of every backing are tagged; elements use their own `ToJson`. -/
run_cmd do
  unless toJson (OrdList.ofList [2, 0]) == json% {"$veil": "set", elements: [0, 2]} &&
      toJson (OrdArray.ofList [2, 0]) == json% {"$veil": "set", elements: [0, 2]} do
    throwError "sorted sets must be tagged sets of their members"
  unless toJson (OrdList.ofList ["b", "a"]) == json% {"$veil": "set", elements: ["a", "b"]} &&
      toJson (OrdArray.ofList ["b", "a"]) == json% {"$veil": "set", elements: ["a", "b"]} do
    throwError "sorted sets must serialize strings as strings, not as their `Repr`"
  unless reprStr (OrdList.ofList [2, 0]) == "{0, 2}" && reprStr (OrdArray.ofList [2, 0]) == "{0, 2}" do
    throwError "sorted sets must show as sets in `Repr` too"
  let subsets := Json.arr <| #[[], [0], [1], [0, 1]].map fun (xs : List Nat) =>
    ValueDisplay.setJson toJson xs.toArray
  unless toJson (Enumeration.allValues (α := OrdList (Fin 2))) == subsets &&
      toJson (Enumeration.allValues (α := OrdArray (Fin 2))) == subsets do
    throwError "sorted set enumeration changed"
  let q : Quorum (Fin 3) := ⟨BitVecAsFinset.ofList [0, 2], by decide⟩
  unless toJson (BitVecAsFinset.ofList ([0, 2] : List (Fin 3))) ==
      json% {"$veil": "set", elements: [0, 2]} && toJson q == toJson q.val do
    throwError "bit sets, and the quorums built on them, must be tagged sets"
  let setExpected := json% {"$veil": "set", elements: [0]}
  unless toJson (fun (_ : Fin 1) => true) == setExpected &&
      toJson ((Std.TreeSet.empty : Std.TreeSet Nat).insert 0) == setExpected &&
      toJson ((Std.ExtTreeSet.empty : Std.ExtTreeSet Nat).insert 0) == setExpected &&
      toJson ((Std.HashSet.emptyWithCapacity : Std.HashSet Nat).insert 0) == setExpected do
    throwError "predicates and tree and hash sets must be tagged sets"
  let mapExpected := json% {"$veil": "map", entries: [{key: 0, value: 7}]}
  unless toJson (fun (_ : Fin 1) => (7 : Nat)) == mapExpected &&
      toJson ((Std.TreeMap.empty : Std.TreeMap Nat Nat).insert 0 7) == mapExpected &&
      toJson ((Std.ExtTreeMap.empty : Std.ExtTreeMap Nat Nat).insert 0 7) == mapExpected &&
      toJson ((Std.HashMap.emptyWithCapacity : Std.HashMap Nat Nat).insert 0 7) == mapExpected do
    throwError "functions and tree and hash maps must be tagged maps"

/-! In `Repr` too, functions over finite domains are maps and predicates are sets; a function of
several arguments is keyed by tuples. -/
run_cmd do
  unless reprStr (fun (a : Fin 3) => a.val * 2) == "{0 ↦ 0, 1 ↦ 2, 2 ↦ 4}" &&
      reprStr (fun (a : Fin 3) => a == 1) == "{1}" &&
      reprStr (fun (_ : Fin 2) => false) == "{}" &&
      reprStr (fun (a b : Fin 2) => a.val + b.val) ==
        "{(0, 0) ↦ 0, (0, 1) ↦ 1, (1, 0) ↦ 1, (1, 1) ↦ 2}" &&
      reprStr (fun (a b : Fin 2) => a == b) == "{(0, 0), (1, 1)}" do
    throwError "finite functions must show as maps, and predicates as sets"

/-! `Display`, which traces and counterexamples show, keeps the structure of numbers, sequences and
containers, and shows any other value by its `Repr`: `some a` differs from `a`, a tuple is not a
list, and a string is quoted. -/
run_cmd do
  let disp {α} [Display α] (a : α) : Json := Display.display a
  unless disp (7 : Nat) == json% 7 && disp true == json% true && disp (2 : Fin 3) == json% 2 &&
      disp (some (7 : Nat)) == json% "some 7" && disp (none : Option Nat) == json% "none" &&
      disp ((0, 1) : Fin 2 × Fin 2) == json% "(0, 1)" && disp "abc" == json% "\"abc\"" &&
      disp () == json% "()" && disp [some (1 : Nat), none] == json% ["some 1", "none"] do
    throwError "Display must keep numbers and sequences, and show other values by their Repr"
  let m : ArrayAsFinmap (Fin 2) (Option Nat) := FinmapLike.insert 1 (some 7) default
  unless disp m == json% {"$veil": "map", entries: [{key: 0, value: "none"},
        {key: 1, value: "some 7"}]} &&
      disp (fun (a b : Fin 2) => a == b) == json% {"$veil": "set", elements: ["(0, 0)", "(1, 1)"]} &&
      disp (OrdList.ofList ["b", "a"]) == json% {"$veil": "set", elements: ["\"a\"", "\"b\""]} do
    throwError "containers must show their elements by Display"
  let .str long := disp (some (List.replicate 40 "abcdef")) | throwError "a Repr must show as a string"
  if long.contains '\n' then
    throwError "a Repr must show on one line, as the text output cannot re-wrap it"

/-- A derived `Display` of an inductive type, as for a module's labels. An argument without a
structured `Display` falls back to `Repr`, so it needs `Repr` of the type parameter: `o` shows
`some 1`, not `some <unrepresentable>`. -/
inductive Lbl (node : Type) where
  | send (n : node) (o : Option node)
  | tick
  deriving Repr, Display

run_cmd do
  unless Display.display (Lbl.send (0 : Fin 2) (some 1)) == json% {send: {n: 0, o: "some 1"}} &&
      Display.display (Lbl.tick : Lbl (Fin 2)) == json% "tick" do
    throwError "a derived Display must show each argument by its Display"

/-! A multiset shows each distinct element with its actual multiplicity; the storage keeps the
multiplicity minus one. -/
run_cmd do
  let bag : TMapMultiset Nat := TMultiset.insert 2 (TMultiset.insert 2 (TMultiset.insert 1 TMultiset.empty))
  unless toJson bag == json% {"$veil": "multiset", entries: [{element: 1, count: 1},
        {element: 2, count: 2}]} && reprStr bag == "{1 × 1, 2 × 2}" do
    throwError "multiset display must show actual multiplicities"
  unless decide (2 ∈ bag) && !decide (3 ∈ bag) do
    throwError "multiset membership changed"
  let bag := TMultiset.remove 2 bag
  unless TMultiset.count 2 bag == 1 && TMultiset.size bag == 2 &&
      toJson bag == json% {"$veil": "multiset", entries: [{element: 1, count: 1},
        {element: 2, count: 1}]} do
    throwError "multiset removal changed its semantics"
  let empty : TMapMultiset Nat := TMultiset.empty
  unless toJson empty == json% {"$veil": "multiset", entries: []} && reprStr empty == "{}" do
    throwError "empty multiset must display as empty"
  let pairs : TMapMultiset (Nat × Nat) :=
    TMultiset.insert (1, 2) (TMultiset.insert (1, 2) TMultiset.empty)
  unless toJson pairs == json% {"$veil": "multiset", entries: [{element: [1, 2], count: 2}]} &&
      reprStr pairs == "{(1, 2) × 2}" do
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

/-! The text of traces renders the tags in set notation, nested anywhere; other JSON reads as `[…]`
and `{k: v}` in key order, with strings verbatim. Unknown or malformed tags are ordinary objects. -/
/--
info: {0, 2}
{[0, 0] ↦ 7}
{1 × 1, 2 × 2}
[{}, {0, 1}]
{{0, 1} ↦ {2, 3}}
{}
[]
{a: [2, x y], b: 1}
{$veil: unknown, elements: []}
{$veil: set, elements: [], extra: true}
{$veil: map, entries: [{key: 0}]}
{$veil: multiset, entries: [{count: -1, element: 0}]}
-/
#guard_msgs in
#eval do
  for j in [toJson (BitVecAsFinset.ofList ([0, 2] : List (Fin 3))),
      toJson (FinmapLike.insert (0, 0) 7 (default : ArrayAsFinmap (Fin 1 × Fin 1) Nat)),
      ValueDisplay.multisetJson toJson #[((1 : Nat), 1), (2, 2)],
      toJson ([BitVecAsFinset.ofList [], BitVecAsFinset.ofList [0, 1]] : List (BitVecAsFinset (Fin 2))),
      ValueDisplay.mapJson toJson toJson #[(OrdList.ofList [(0 : Nat), 1], OrdList.ofList [(2 : Nat), 3])],
      ValueDisplay.setJson toJson (#[] : Array Nat), toJson ([] : List Nat),
      json% {b: 1, a: [2, "x y"]},
      json% {"$veil": "unknown", elements: []},
      json% {"$veil": "set", elements: [], extra: true},
      json% {"$veil": "map", entries: [{key: 0}]},
      json% {"$veil": "multiset", entries: [{element: 0, count: -1}]}] do
    IO.println (ValueDisplay.formatJson j)

/-! Long values fill lines up to `ValueDisplay.textWidth` and continue aligned: after `key = `,
after an opening bracket, after `k ↦ `, and after the `(` of an action label. -/
/--
info: big = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
       26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44}
wide = {0 ↦ {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
             24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35},
        1 ↦ {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
             24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36}}
decide(b=1,
       q={0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
          25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39})
-/
#guard_msgs in
#eval do
  IO.println (ValueDisplay.formatField "" "big" (ValueDisplay.setJson toJson (Array.range 45)))
  IO.println (ValueDisplay.formatField "" "wide" (ValueDisplay.mapJson toJson id
    ((Array.range 2).map fun i => (i, ValueDisplay.setJson toJson (Array.range (36 + i))))))
  IO.println ((ValueDisplay.callFormat "decide" [("b", toJson (1 : Nat)),
    ("q", ValueDisplay.setJson toJson (Array.range 40))]).pretty ValueDisplay.textWidth)

-- The generator rejects ambiguous storage rather than silently dropping data.
structure TwoPayloads where
  first : Nat
  second : Nat

/-- error: Expected a structure with exactly one non-proof field -/
#guard_msgs in
veil_derive_wrapper_instances TwoPayloads

end ValueDisplayRegression

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
  unless json.getObjValD "values" == json% {"$veil": "map", entries: [{key: 0, value: null},
        {key: 1, value: 7}]} &&
      json.getObjValD "selected" == json% {"$veil": "set", elements: [1]} do
    throwError "state JSON must use the field representations' instances: {json}"

end DirectContainerJson
