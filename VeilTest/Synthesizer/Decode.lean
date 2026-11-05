module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Model

/-! The model decoder of `#synthesize_invariants` against the `ToJson` serialization of Veil values.

Each case serializes a Lean function with `ToJson`, as `VeilTrace.toJson evalExprToJson` does for
the components of a solver model, decodes it with `Model.table` or `Model.numTable`, and compares
the result with the tuples computed from the function itself. Functions of `n ≥ 2` arguments are
uncurried one argument at a time, so their keys are left-nested arrays such as `[[0, 1], 2]`. -/

meta section
open Lean Veil Veil.Synthesizer Veil.Synthesizer.Model

/-- An enum, serialized by its constructors' bare names as Veil's `enum` types are. -/
inductive Ph where
  | Idle | Busy | Done
deriving DecidableEq, Inhabited, Hashable, Ord, Repr, ToJson

instance : Enumeration Ph where
  allValues := [.Idle, .Busy, .Done]
  complete := by intro x; cases x <;> simp

abbrev N := Fin 3

def phCtors : Array Name := #[`Ph.Idle, `Ph.Busy, `Ph.Done]

/-- Three nodes and the enum `Ph`. -/
def carrier : FinStructure :=
  { sorts := #[(`node, 3), (`Ph, 3)], enums := #[(`Ph, phCtors)], rels := #[] }

def nodes : List N := [0, 1, 2]
def phs : List Ph := [.Idle, .Busy, .Done]
def ph (p : Ph) : Nat := match p with | .Idle => 0 | .Busy => 1 | .Done => 2

/-- Whether decoding `j` as a relation over `argSorts` gives exactly the rows `expected`. -/
def relDecodes (argSorts : Array SortName) (j : Json) (expected : List (Array Nat)) : Bool :=
  match table carrier { name := `r, argSorts } j with
  | .ok rows => rows.size == expected.length && expected.all rows.contains
  | .error _ => false

/-- Whether decoding `j` as a function with argument and result sorts `sorts` gives exactly the
graph `expected`. -/
def fnDecodes (sorts : Array SortName) (j : Json) (expected : List (Array Nat)) : Bool :=
  match table carrier { name := `f, argSorts := sorts, isFunction := true } j with
  | .ok rows => rows.size == expected.length && expected.all rows.contains
  | .error _ => false

/-- The decoding error for `j` as a relation over `argSorts`, if there is one. -/
def relError (argSorts : Array SortName) (j : Json) : String :=
  match table carrier { name := `r, argSorts } j with
  | .ok rows => s!"decoded {rows}"
  | .error e => e

/-! ## Tuples -/

/-- The leaves of `j`, compressed and separated by spaces. -/
def leavesOf (j : Json) : String := " ".intercalate ((leaves j).map (·.compress)).toList

def n (k : Nat) : Json := .num k

/-- info: "0 1 2 0" -/
#guard_msgs in #eval leavesOf (toJson ((((0 : N), (1 : N)), (2 : N)), (0 : N)))
/-- info: "0 1 2" -/
#guard_msgs in #eval leavesOf (toJson ((0 : N), (1 : N), (2 : N)))
/-- info: "0 \"Busy\" 2" -/
#guard_msgs in #eval leavesOf (toJson (((0 : N), Ph.Busy), (2 : N)))
/-- info: "-3" -/
#guard_msgs in #eval leavesOf (toJson (-3 : Int))
/-- info: "\"Done\"" -/
#guard_msgs in #eval leavesOf (toJson Ph.Done)

/-! ## Relations over uninterpreted sorts, arities 1 to 4 -/

def r1 (x : N) : Bool := x = 1
def r2 (x y : N) : Bool := x ≠ y && x.val ≤ 1
def r3 (x y z : N) : Bool := (x.val + y.val + z.val) % 3 == 1
def r4 (x y z w : N) : Bool := x = w && y ≠ z && (x.val + y.val) % 2 == 0

#guard relDecodes #[`node] (toJson r1)
  (nodes.filter r1 |>.map fun x ↦ #[x.val])
#guard relDecodes #[`node, `node] (toJson r2)
  (nodes.flatMap fun x ↦ nodes.filter (r2 x) |>.map fun y ↦ #[x.val, y.val])
#guard relDecodes #[`node, `node, `node] (toJson r3)
  (nodes.flatMap fun x ↦ nodes.flatMap fun y ↦ nodes.filter (r3 x y) |>.map fun z ↦
    #[x.val, y.val, z.val])
#guard relDecodes #[`node, `node, `node, `node] (toJson r4)
  (nodes.flatMap fun x ↦ nodes.flatMap fun y ↦ nodes.flatMap fun z ↦
    nodes.filter (r4 x y z) |>.map fun w ↦ #[x.val, y.val, z.val, w.val])

-- The full and the empty ternary relation.
#guard relDecodes #[`node, `node, `node] (toJson fun (_ _ _ : N) ↦ true)
  (nodes.flatMap fun x ↦ nodes.flatMap fun y ↦ nodes.map fun z ↦ #[x.val, y.val, z.val])
#guard relDecodes #[`node, `node, `node] (toJson fun (_ _ _ : N) ↦ false) []

/-! ## Relations with enum arguments -/

def rp (p : Ph) (x : N) : Bool := p = .Done && x ≠ 0
def rpn (x : N) (p : Ph) (y : N) : Bool := x = y && p ≠ .Idle

#guard relDecodes #[`Ph, `node] (toJson rp)
  (phs.flatMap fun p ↦ nodes.filter (rp p) |>.map fun x ↦ #[ph p, x.val])
#guard relDecodes #[`node, `Ph, `node] (toJson rpn)
  (nodes.flatMap fun x ↦ phs.flatMap fun p ↦ nodes.filter (rpn x p) |>.map fun y ↦
    #[x.val, ph p, y.val])

/-! ## Functions -/

def f1 (x : N) : N := x + 1
def f2 (x y : N) : N := if x = 0 then y else x
def f3 (x y z : N) : N := x + y * z
def fp (x : N) : Ph := if x = 0 then .Idle else .Done

#guard fnDecodes #[`node, `node] (toJson f1)
  (nodes.map fun x ↦ #[x.val, (f1 x).val])
#guard fnDecodes #[`node, `node, `node] (toJson f2)
  (nodes.flatMap fun x ↦ nodes.map fun y ↦ #[x.val, y.val, (f2 x y).val])
#guard fnDecodes #[`node, `node, `node, `node] (toJson f3)
  (nodes.flatMap fun x ↦ nodes.flatMap fun y ↦ nodes.map fun z ↦
    #[x.val, y.val, z.val, (f3 x y z).val])
#guard fnDecodes #[`node, `Ph] (toJson fp)
  (nodes.map fun x ↦ #[x.val, ph (fp x)])

/-! ## Integer-valued functions -/

def fi (x y : N) : Int := if x = y then -3 else x.val - y.val
def fi3 (x y z : N) : Int := x.val * 10 - y.val - z.val

#guard match numTable carrier { name := `fi, argSorts := #[`node, `node, `Int] }
    (toJson fi) with
  | .ok rows => rows.size == 9 &&
      (nodes.all fun x ↦ nodes.all fun y ↦ rows.contains (#[x.val, y.val], fi x y))
  | .error _ => false
#guard match numTable carrier { name := `fi3, argSorts := #[`node, `node, `node, `Int] }
    (toJson fi3) with
  | .ok rows => rows.size == 27 &&
      (nodes.all fun x ↦ nodes.all fun y ↦ nodes.all fun z ↦
        rows.contains (#[x.val, y.val, z.val], fi3 x y z))
  | .error _ => false

/-! ## Malformed input is reported, not misread -/

/-- A tagged set of the given tuples. -/
def setOf (elems : Array Json) : Json :=
  Json.mkObj [("$veil", "set"), ("elements", .arr elems)]

def wrongArity : String := relError #[`node, `node, `node] (toJson r2)
def outOfRange : String := relError #[`node, `node] (setOf #[.arr #[n 0, n 3]])
def tooLong : String := relError #[`node, `node] (setOf #[.arr #[.arr #[n 0, n 1], n 2]])
def unknownCtor : String :=
  match table { carrier with enums := #[(`Ph, #[`Ph.Busy, `Ph.Done])] }
      { name := `r, argSorts := #[`Ph, `node] }
      (toJson fun (p : Ph) (x : N) ↦ p == .Idle && x == 0) with
  | .ok _ => "decoded"
  | .error e => e

/-- info: "tuple of wrong shape #[0, 1] (expected arity 3)" -/
#guard_msgs in #eval wrongArity
/-- info: "element 3 of sort node is out of range; the sort has 3 element(s)" -/
#guard_msgs in #eval outOfRange
/-- info: "tuple of wrong shape #[0, 1, 2] (expected arity 2)" -/
#guard_msgs in #eval tooLong
/-- info: "Idle is not a constructor of enum sort Ph" -/
#guard_msgs in #eval unknownCtor

end
