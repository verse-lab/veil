module

public import Lean.Data.Json.FromToJson.Basic

@[expose] public section

/-! Display helpers shared by the concrete containers, which pass their logical contents (members,
entries, multiplicities) rather than their storage. The `Repr` helpers take lists, as
`Std.Format.joinSep` does; the JSON helpers take arrays, as `Lean.Json.arr` does, and map over them
in place. -/

namespace Veil.ContainerDisplay

/-- Render logical set members, independently of the storage representation. -/
def setFormat [Repr α] (members : List α) : Std.Format :=
  Std.Format.bracket "{" (Std.Format.joinSep (members.map repr) ("," ++ Std.Format.line)) "}"

/-- Render logical map entries, independently of the storage representation. -/
def mapFormat [Repr α] [Repr β] (entries : List (α × β)) : Std.Format :=
  Std.Format.bracket "{" (Std.Format.joinSep
    (entries.map fun (k, v) => repr k ++ " ↦ " ++ repr v) ("," ++ Std.Format.line)) "}"

/-- Render distinct multiset elements with their logical multiplicities, without expanding them. -/
def multisetFormat [Repr α] (entries : List (α × Nat)) : Std.Format :=
  Std.Format.bracket "{" (Std.Format.joinSep
    (entries.map fun (a, n) => repr a ++ " × " ++ repr n) ("," ++ Std.Format.line)) "}"

/-- Set members as a JSON array. -/
def setJson [Lean.ToJson α] (members : Array α) : Lean.Json :=
  Lean.Json.arr <| members.map Lean.toJson

/-- Finite-map entries in Veil's finite-function JSON convention: one array per entry, holding the
key followed by the value. A key that is itself an array, e.g. a tuple, is flattened, so a function
`(a, b) ↦ c` gives `[a, b, c]` rather than `[[a, b], c]`. -/
def mapJson [Lean.ToJson α] [Lean.ToJson β] (entries : Array (α × β)) : Lean.Json :=
  Lean.Json.arr <| entries.map fun (k, v) =>
    match Lean.toJson k with
    | .arr keys => .arr (keys.push (Lean.toJson v))
    | key => .arr #[key, Lean.toJson v]

/-- Multiset entries as `[element, multiplicity]` pairs. Unlike `mapJson`, an element that is itself
an array (a tuple, a list) stays whole: it is one value, not the arguments of a function. -/
def multisetJson [Lean.ToJson α] (entries : Array (α × Nat)) : Lean.Json :=
  Lean.Json.arr <| entries.map fun (a, n) => .arr #[Lean.toJson a, Lean.toJson n]

end Veil.ContainerDisplay
