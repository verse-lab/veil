module

public meta import Lean
public meta import Veil.Core.Tools.Synthesizer.Structure
public meta import Veil.Core.Tools.Synthesizer.Vocabulary

/-!
# Reading solver models

Veil decodes a solver model of a trace query into a `VeilTrace` and renders it as JSON
(`VeilTrace.toJson`). This file reads that JSON as finite structures over a `Signature`.

## Main definitions

* `Veil.Synthesizer.DecodedTrace`: the structures and labels of a decoded trace.
* `Veil.Synthesizer.decodeTrace`: decode `VeilTrace.toJson` output.

## Implementation notes

The JSON gives the size of each uninterpreted sort as its instantiation `Fin n`, each state's
components under `states[i].fields`, the immutable components under `theory` and the class
symbols under `extraVals`. A relation is a list of tuples, nested to the left, a `Bool` individual
a boolean, a function a list of rows `[args, value]`, an individual a bare value, and an element
of an enum sort its constructor's name.

A class symbol that no axiom mentions occurs in no hypothesis of a query, so the solver may leave
it out of the model, and any table completes it. Such a symbol gets the empty relation, or the
function to element `0`, and is listed in `DecodedTrace.completed`.
-/

public meta section

namespace Veil.Synthesizer
open Lean

namespace Model

/-- The size `n` of a sort instantiated at `Fin n`. -/
def parseFin? (s : String) : Option Nat :=
  if s.startsWith "Fin " then (s.drop 4).trimAscii.toNat? else none

/-- A JSON integer. -/
def intOfJson? : Json → Option Int
  | .num n => if n.exponent == 0 then some n.mantissa else none
  | _ => none

/-- A JSON natural number. -/
def natOfJson? (j : Json) : Option Nat :=
  (intOfJson? j).bind fun n ↦ if n ≥ 0 then n.toNat else none

/-- The leaves of a nested JSON array, in order. -/
partial def leaves : Json → Array Json
  | .arr xs => xs.flatMap leaves
  | j => #[j]

variable (m : FinStructure)

/-- An element of sort `s`: an index for an uninterpreted sort, a constructor name for an enum
sort. `m` gives the sort sizes and enums. -/
def element (s : SortName) (j : Json) : Except String Nat :=
  match m.enums.find? (·.1 == s), j with
  | some (_, ctors), .str name =>
    match ctors.findIdx? (ctorBaseName · == name) with
    | some i => pure i
    | none => throw s!"{name} is not a constructor of enum sort {s}"
  | some _, _ =>
    throw s!"element {j} of enum sort {s} is not a constructor name; the model did not resolve \
      the enum sort to its concrete type"
  | none, _ =>
    match natOfJson? j with
    | some v =>
      if v < m.sortSize s then pure v
      else throw s!"element {v} of sort {s} is out of range; the sort has {m.sortSize s} element(s)"
    | none => throw s!"element {j} of sort {s} is not an index"

/-- Fail unless `rows` has exactly one row per tuple of elements of `argSorts`. -/
def checkTotal (argSorts : Array SortName) (rows : Array (Array Nat)) : Except String Unit := do
  let domain := m.tuples argSorts
  unless rows.size == domain.size && domain.all rows.contains do
    throw s!"function table has {rows.size} row(s) for {domain.size} argument tuple(s); it must \
      be total"

/-- The table of a symbol: a list of tuples, a boolean for a 0-ary relation, a bare value for an
individual. A function's table must be total. -/
def table (sym : Symbol) (j : Json) : Except String (Array (Array Nat)) := do
  let sorts := sym.argSorts
  let rows ← match j with
    | .bool b =>
      if sorts.isEmpty then pure (if b then #[#[]] else #[])
      else throw "boolean for a symbol of arity > 0"
    | .arr rows => rows.mapM fun row ↦ do
      let ls := leaves row
      unless ls.size == sorts.size do
        throw s!"tuple of wrong shape {row} (expected arity {sorts.size})"
      (sorts.zip ls).mapM fun (s, l) ↦ element m s l
    | j =>
      if sorts.size == 1 then return #[#[← element m sorts[0]! j]]
      else throw s!"scalar {j} for a symbol of arity ≠ 1"
  if sym.isFunction then checkTotal m sorts.pop (rows.map (·.pop))
  return rows

/-- The value table of a numeric symbol: an integer for an individual, a total list of rows
`[args, value]` for a function. -/
def numTable (sym : Symbol) (j : Json) : Except String (Array (Array Nat × Int)) := do
  let argSorts := sym.argSorts.pop
  let value (j : Json) : Except String Int := match intOfJson? j with
    | some v => pure v
    | none => throw s!"value {j} is not an integer"
  if argSorts.isEmpty then return #[(#[], ← value j)]
  let .arr rows := j | throw s!"{j} is not a function table"
  let rows ← rows.mapM fun row ↦ do
    let ls := leaves row
    unless ls.size == argSorts.size + 1 do
      throw s!"row of wrong shape {row} (expected {argSorts.size} argument(s) and a value)"
    return (← (argSorts.zip ls.pop).mapM fun (s, l) ↦ element m s l, ← value ls.back!)
  checkTotal m argSorts (rows.map (·.1))
  return rows

/-- The table of a class symbol the model leaves out: the empty relation, or the function to
element `0`. -/
def defaultTable (sym : Symbol) : Array (Array Nat) :=
  if sym.isFunction then (m.tuples sym.argSorts.pop).map (·.push 0) else #[]

/-- Add the table of component `sym`, read from `j`, to `m`. -/
def addComponent (sym : Symbol) (j : Json) : Except String FinStructure :=
  if sym.isNumeric then return { m with nums := m.nums.push (sym, ← numTable m sym j) }
  else return { m with rels := m.rels.push (sym, ← table m sym j) }

end Model

open Model in
/-- The structure of one state: the state components from `fields`, the immutable components from
`theory`, the class symbols from `extraVals`. Also returns the class symbols the model left out. -/
def structureOfState (sig : Signature) (carrier : FinStructure)
    (fields theoryJson extraVals : Json) : Except String (FinStructure × Array Name) := do
  let mut m := carrier
  for sym in sig.stateSymbols do
    let .ok v := fields.getObjVal? sym.name.toString | throw s!"state has no field {sym.name}"
    m ← addComponent m sym v |>.mapError (s!"field {sym.name}: " ++ ·)
  for sym in sig.theorySymbols do
    let .ok v := theoryJson.getObjVal? sym.name.toString
      | throw s!"model theory has no field {sym.name}"
    m ← addComponent m sym v |>.mapError (s!"theory field {sym.name}: " ++ ·)
  let mut completed := #[]
  for sym in sig.classSymbols do
    let key := sym.key.toString
    if let .ok v := extraVals.getObjVal? key then
      let rows ← table carrier sym v |>.mapError (s!"symbol {key}: " ++ ·)
      m := { m with rels := m.rels.push (sym, rows) }
      continue
    -- A key of the same instance ending in the field's name is a projection path the vocabulary
    -- did not expect, not a missing symbol.
    let pre := s!"{(sym.inst?.getD .anonymous)}."
    let suffix := s!".{sym.name}"
    let projection? : Option String := match extraVals with
      | .obj kvs =>
        (kvs.toArray.find? fun (k, _) ↦ k.startsWith pre && k.endsWith suffix).map (·.1)
      | _ => none
    if let some k := projection? then throw s!"model names {k} where the vocabulary expected {key}"
    unless sig.freeClassSymbols.contains sym.key do
      throw s!"the model does not mention {key}, which an axiom of its class constrains; every \
        such symbol is declared in the query and reported by the solver"
    completed := completed.push sym.key
    m := { m with rels := m.rels.push (sym, defaultTable carrier sym) }
  return (m, completed)

/-- The structures and labels of a decoded trace. -/
structure DecodedTrace where
  sorts : Array (SortName × Nat)
  states : Array FinStructure
  /-- The label of the transition into each state (`{"recv": {…}}`), kept opaque. -/
  labels : Array Json
  /-- The class symbols the model left out, completed by `Model.defaultTable`. -/
  completed : Array Name := #[]
deriving Inhabited

/-- Decode `VeilTrace.toJson` output over the signature `sig`. -/
def decodeTrace (sig : Signature) (j : Json) : Except String DecodedTrace := do
  let inst ← j.getObjVal? "instantiation" |>.mapError toString
  let extraVals := (j.getObjVal? "extraVals").toOption.getD (.obj {})
  let theoryJson := (j.getObjVal? "theory").toOption.getD (.obj {})
  let sorts ← sig.sorts.mapM fun s ↦ do
    if let some (_, ctors) := sig.enums.find? (·.1 == s) then return (s, ctors.size)
    match inst.getObjVal? s.toString with
    | .ok (.str t) =>
      let some n := Model.parseFin? t | throw s!"sort {s} instantiated at non-Fin type {t}"
      return (s, n)
    | _ => throw s!"instantiation lacks sort {s}"
  let carrier : FinStructure := { sorts, enums := sig.enums, rels := #[] }
  let .arr states ← j.getObjVal? "states" |>.mapError toString | throw "states is not an array"
  let decoded ← states.mapM fun st ↦ do
    let fields ← st.getObjVal? "fields" |>.mapError toString
    structureOfState sig carrier fields theoryJson extraVals
  return {
    sorts, states := decoded.map (·.1)
    labels := states.map fun st ↦ (st.getObjVal? "transition").toOption.getD .null
    completed := (decoded.flatMap (·.2)).toList.eraseDups.toArray }

end Veil.Synthesizer
