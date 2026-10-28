module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Model

/-! Randomized round-trips through the model decoder of `#updr`.

Each case builds a pseudo-random relation or function over `Fin n` (`n` from 1 to 4) and an enum,
of 1 to 4 arguments, serializes it with `ToJson` as `VeilTrace.toJson evalExprToJson` does, decodes
it with `Model.table` or `Model.numTable`, and compares the decoded table with the one computed
from the function. The density of each relation depends on the seed, so the cases include the
empty and the full relation. -/

meta section
open Lean Veil Veil.Synthesizer Veil.Synthesizer.Model

inductive Ph where
  | Idle | Busy | Done
deriving DecidableEq, Inhabited, Hashable, Ord, Repr, ToJson

instance : Enumeration Ph where
  allValues := [.Idle, .Busy, .Done]
  complete := by intro x; cases x <;> simp

def Ph.idx : Ph → Nat | .Idle => 0 | .Busy => 1 | .Done => 2

def phCtors : Array Name := #[`Ph.Idle, `Ph.Busy, `Ph.Done]

/-- `n` nodes and the enum `Ph`. -/
def carrierOf (n : Nat) : FinStructure :=
  { sorts := #[(`node, n), (`Ph, 3)], enums := #[(`Ph, phCtors)], rels := #[] }

/-! ## Pseudo-random tables -/

/-- A pseudo-random number for the tuple `xs` under `seed`. -/
def rnd (seed : Nat) (xs : List Nat) : Nat := (hash (seed, xs)).toNat

/-- Whether the relation of `seed` holds on `xs`: from never (`seed % 6 = 0`) to always
(`seed % 6 = 5`). -/
def bit (seed : Nat) (xs : List Nat) : Bool := rnd seed xs % 5 < seed % 6

/-- All tuples of the given sort sizes, as lists. -/
def tuplesOf : List Nat → List (List Nat)
  | [] => [[]]
  | k :: ks => (List.range k).flatMap fun i ↦ (tuplesOf ks).map (i :: ·)

def lexLt (a b : Array Nat) : Bool := a.toList < b.toList

def sorted (rows : Array (Array Nat)) : Array (Array Nat) := rows.qsort lexLt

/-- Whether decoding `j` as `sym` over `n` nodes gives exactly `expected`, in any order. -/
def decodes (n : Nat) (sym : Symbol) (j : Json) (expected : List (List Nat)) : Bool :=
  match table (carrierOf n) sym j with
  | .ok rows => sorted rows == sorted (expected.toArray.map List.toArray)
  | .error _ => false

/-- Whether decoding `j` as the integer-valued `sym` over `n` nodes gives exactly `expected`. -/
def numDecodes (n : Nat) (sym : Symbol) (j : Json) (expected : List (List Nat × Int)) : Bool :=
  match numTable (carrierOf n) sym j with
  | .ok rows =>
    let key (r : Array Nat × Int) : Array Nat := r.1.push (r.2 + 1000).toNat
    sorted (rows.map key) == sorted (expected.toArray.map fun (a, v) ↦ key (a.toArray, v))
  | .error _ => false

def seeds : List Nat := List.range 12
def sizes : List Nat := [1, 2, 3, 4]

def rel (k : Nat) : Symbol := { name := `r, argSorts := Array.replicate k `node }
def fn (k : Nat) (res : SortName) : Symbol :=
  { name := `f, argSorts := (Array.replicate k `node).push res, isFunction := true }

/-! ## Relations over `Fin n` -/

#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n (rel 1) (toJson fun (a : Fin n) ↦ bit s [a])
    ((tuplesOf [n]).filter (bit s))
#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n (rel 2) (toJson fun (a b : Fin n) ↦ bit s [a, b])
    ((tuplesOf [n, n]).filter (bit s))
#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n (rel 3) (toJson fun (a b c : Fin n) ↦ bit s [a, b, c])
    ((tuplesOf [n, n, n]).filter (bit s))
#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n (rel 4) (toJson fun (a b c d : Fin n) ↦ bit s [a, b, c, d])
    ((tuplesOf [n, n, n, n]).filter (bit s))

/-! ## Relations mixing `Fin n` and an enum, in every position -/

#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n { name := `r, argSorts := #[`Ph, `node, `node] }
    (toJson fun (p : Ph) (a b : Fin n) ↦ bit s [p.idx, a, b])
    ((tuplesOf [3, n, n]).filter (bit s))
#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n { name := `r, argSorts := #[`node, `Ph, `node, `Ph] }
    (toJson fun (a : Fin n) (p : Ph) (b : Fin n) (q : Ph) ↦ bit s [a, p.idx, b, q.idx])
    ((tuplesOf [n, 3, n, 3]).filter (bit s))
#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n { name := `r, argSorts := #[`node, `node, `Ph] }
    (toJson fun (a b : Fin n) (p : Ph) ↦ bit s [a, b, p.idx])
    ((tuplesOf [n, n, 3]).filter (bit s))

/-! ## Functions into `Fin n`, an enum, and `Int` -/

def toPh (k : Nat) : Ph := match k % 3 with | 0 => .Idle | 1 => .Busy | _ => .Done

/-- The node `k mod n` of the `n` nodes, which are not empty since they contain `a`. -/
def nodeOf (a : Fin n) (k : Nat) : Fin n :=
  ⟨k % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt)⟩
def toInt (k : Nat) : Int := (k % 21 : Nat) - 10

#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n (fn 1 `node) (toJson fun (a : Fin n) ↦ nodeOf a (rnd s [a]))
    ((tuplesOf [n]).map fun xs ↦ xs ++ [rnd s xs % n])
#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n (fn 2 `node) (toJson fun (a b : Fin n) ↦ nodeOf a (rnd s [a, b]))
    ((tuplesOf [n, n]).map fun xs ↦ xs ++ [rnd s xs % n])
#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n (fn 3 `node) (toJson fun (a b c : Fin n) ↦ nodeOf a (rnd s [a, b, c]))
    ((tuplesOf [n, n, n]).map fun xs ↦ xs ++ [rnd s xs % n])
#guard sizes.all fun n ↦ seeds.all fun s ↦
  decodes n (fn 3 `Ph) (toJson fun (a b c : Fin n) ↦ toPh (rnd s [a, b, c]))
    ((tuplesOf [n, n, n]).map fun xs ↦ xs ++ [(toPh (rnd s xs)).idx])
#guard sizes.all fun n ↦ seeds.all fun s ↦
  numDecodes n { name := `f, argSorts := #[`node, `Int] }
    (toJson fun (a : Fin n) ↦ toInt (rnd s [a]))
    ((tuplesOf [n]).map fun xs ↦ (xs, toInt (rnd s xs)))
#guard sizes.all fun n ↦ seeds.all fun s ↦
  numDecodes n { name := `f, argSorts := #[`node, `node, `node, `Int] }
    (toJson fun (a b c : Fin n) ↦ toInt (rnd s [a, b, c]))
    ((tuplesOf [n, n, n]).map fun xs ↦ (xs, toInt (rnd s xs)))
#guard sizes.all fun n ↦ seeds.all fun s ↦
  numDecodes n { name := `f, argSorts := #[`Ph, `node, `Int] }
    (toJson fun (p : Ph) (a : Fin n) ↦ toInt (rnd s [p.idx, a]))
    ((tuplesOf [3, n]).map fun xs ↦ (xs, toInt (rnd s xs)))

/-! ## Decoding is strict

A table missing a row of a function, or with a row out of range, is an error rather than a smaller
or wrapped table. -/

/-- The tagged map of `f` with its first entry dropped. -/
def dropFirstEntry (j : Json) : Json :=
  match j.getObjVal? "entries" with
  | .ok (.arr es) => Json.mkObj [("$veil", "map"), ("entries", .arr (es.extract 1 es.size))]
  | _ => j

#guard sizes.all fun n ↦ seeds.all fun s ↦
  !decodes n (fn 2 `node)
    (dropFirstEntry <| toJson fun (a b : Fin n) ↦ nodeOf a (rnd s [a, b]))
    ((tuplesOf [n, n]).map fun xs ↦ xs ++ [rnd s xs % n]).tail
-- A relation over `n` nodes decodes over `n - 1` nodes exactly when it avoids the last node.
#guard [2, 3, 4, 5].all fun n ↦ seeds.all fun s ↦
  let rows := (tuplesOf [n, n, n]).filter (bit s)
  decodes (n - 1) (rel 3) (toJson fun (a b c : Fin n) ↦ bit s [a, b, c]) rows ==
    rows.all (·.all (· < n - 1))

end

