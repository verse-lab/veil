module

public import Lean.Data.Json.FromToJson.Basic

@[expose] public section

/-! # Display of values

How Veil displays the values of states, theories and transitions, in the text output of traces and
counterexamples and in the widget: the `Display` class, the `Repr` and JSON helpers of the concrete
containers, the tags of sets, maps and multisets in JSON, and the rendering of JSON as text. The
containers pass their logical contents (members, entries, multiplicities) rather than their storage.

Three classes take part, in different roles:
- `Display` gives the data shown for a value: the parts that the front ends use (the members of a
  set, the elements of a sequence, the fields of a state), and for any other value its `Repr`.
- `ToJson` serializes the messages that carry these values, such as a model-checking result and the
  trace in it: the message is `ToJson`, the values in it are `Display`.
- `Repr` is Lean text: what `#eval` prints, and the fallback of `Display`.

A displayed value goes through two types, also in different roles:
- `Lean.Json` is the data. A value's `Display` produces it, the compiled checker prints it and the
  elaborator reads it back, and the widget receives it; the text output and the widget both render
  from it.
- `Std.Format` is layout: a document of text, `line` breaks, `nest`ing and `group`s, which
  `Std.Format.pretty` lays out at a width, breaking the lines of a group only when the group does
  not fit. `Repr` produces one, and the text output builds one from the JSON just before printing
  it (`renderJson`). It is never serialized: the widget lays out the JSON in its own way.

Put together, the text output takes a value through `Display` to `Lean.Json`, whose leaves are
`Repr`s laid out on one line, then through `renderJson` to `Std.Format`, and through
`Std.Format.pretty` to text. The widget renders the `Lean.Json` itself.

The text output distinguishes values to render from text to display:
- A *value* is data rendered according to its representation (`renderJson`): containers and
  objects are rendered recursively, while numbers, booleans and strings are atomic values. A
  string is the `Repr` of a value whose `Display` is not structured (see `Display` below):
  `some 3`, `"abc"`, `(0, 1)`.
- *Text* is supplied for direct display (`renderText`): result tags (`found_violation`),
  violation kinds, property names, error messages, the seed, type names and already formatted
  picks. Type names are text here because they arrive as printed type expressions.

Both show strings as they are, but keeping their roles separate lets the rendering of values change
without touching text. -/

namespace Veil.ValueDisplay

/-! ## `Repr`: logical contents as Lean text

These take lists, as `Std.Format.joinSep` does. -/

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

/-! ## JSON: tagged containers

Sets, maps and multisets are tagged objects, so that the text output and the widget can show them
as such rather than as sequences:
- `{"$veil": "set", "elements": [x, …]}`
- `{"$veil": "map", "entries": [{"key": k, "value": v}, …]}`
- `{"$veil": "multiset", "entries": [{"element": x, "count": n}, …]}`

`$veil` is reserved for these tags. `collection?` below recognizes them, and so does
`logicalContainer` in `widget/src/veilUtils.tsx`; the two must agree.

These take arrays, as `Lean.Json.arr` does, and map over them in place. They also take the encoding
of the elements: `toJson` for a container's `ToJson`, `Display.display` for its `Display`. -/

def setJson (enc : α → Lean.Json) (members : Array α) : Lean.Json :=
  Lean.Json.mkObj [("$veil", .str "set"), ("elements", .arr (members.map enc))]

/-- Keys stay whole JSON values: a tuple or a container is one key. -/
def mapJson (encKey : α → Lean.Json) (encValue : β → Lean.Json) (entries : Array (α × β)) :
    Lean.Json :=
  Lean.Json.mkObj [("$veil", .str "map"), ("entries", .arr <| entries.map fun (k, v) =>
    Lean.Json.mkObj [("key", encKey k), ("value", encValue v)])]

def multisetJson (enc : α → Lean.Json) (entries : Array (α × Nat)) : Lean.Json :=
  Lean.Json.mkObj [("$veil", .str "multiset"), ("entries", .arr <| entries.map fun (a, n) =>
    Lean.Json.mkObj [("element", enc a), ("count", Lean.toJson n)])]

/-! ## Reading the tags back -/

/-- The kind and the elements or entries of a tagged container. Only complete envelopes count:
an unknown or malformed tag stays an ordinary object. -/
def collection? (j : Lean.Json) : Option (String × Array Lean.Json) := do
  let .obj fields := j | none
  guard (fields.size == 2)
  let .str kind ← (j.getObjVal? "$veil").toOption | none
  let payload ← match kind with
    | "set" => (j.getObjVal? "elements").toOption
    | "map" | "multiset" => (j.getObjVal? "entries").toOption
    | _ => none
  let .arr entries := payload | none
  if kind == "map" then
    guard <| entries.all fun e => match e with
      | .obj fs => fs.size == 2 && (e.getObjVal? "key").isOk && (e.getObjVal? "value").isOk
      | _ => false
  if kind == "multiset" then
    guard <| entries.all fun e => match e with
      | .obj fs => fs.size == 2 && (e.getObjVal? "element").isOk &&
          ((e.getObjVal? "count").bind Lean.Json.getNat?).isOk
      | _ => false
  return (kind, entries)

/-! ## Text output

For `TraceDisplay` and `VerificationResults`. `renderJson`, `renderText`, `callFormat` and
`actionFormat` build a `Std.Format`; `formatJson`, `formatText`, `formatField`, `formatFields` and
`formatAction` lay out one value or one line at `textWidth`, given what precedes it on its line;
the callers only assemble these lines into messages. -/

/-- The width of the text output of traces and counterexamples. -/
def textWidth : Nat := 100

/-- `label` and `sep` followed by `value`, whose continuation lines align after `sep`. The label is
measured as laid out on one line, as it is unless it is very long itself. -/
def labeled (label : Std.Format) (sep : String) (value : Std.Format) : Std.Format :=
  let lead := label ++ sep
  lead ++ Std.Format.nest (lead.pretty 100000).length value

/-- A JSON value as traces and counterexamples show it: tagged containers in set notation (`{a, b}`,
`{k ↦ v}`, `{a × n}`), arrays in brackets, objects as `{k: v}` in key order, strings verbatim.
Elements fill each line, and continue aligned after the opening bracket. -/
partial def renderJson (j : Lean.Json) : Std.Format :=
  match collection? j with
  | some (kind, entries) =>
    let entry (e : Lean.Json) : Std.Format :=
      if kind == "map" then labeled (renderJson (e.getObjValD "key")) " ↦ " (renderJson (e.getObjValD "value"))
      else if kind == "multiset" then
        renderJson (e.getObjValD "element") ++ " × " ++ renderJson (e.getObjValD "count")
      else renderJson e
    seq "{" (entries.toList.map entry) "}"
  | none => match j with
    | .arr elems => seq "[" (elems.toList.map renderJson) "]"
    | .obj kvs => seq "{" (kvs.toList.map fun (k, v) => labeled (Std.Format.text k) ": " (renderJson v)) "}"
    | .str s => s
    | _ => j.compress
where
  seq (l : String) (parts : List Std.Format) (r : String) : Std.Format :=
    Std.Format.bracketFill l (Std.Format.joinSep parts ("," ++ Std.Format.line)) r

/-- Text rather than a value: a string shows as it is, and anything else as a value. Result tags,
property names, error messages, picks and type names are text. -/
def renderText (j : Lean.Json) : Std.Format := match j with
  | .str s => s
  | _ => renderJson j

/-- `name(k=v, …)`, as action labels are shown; long arguments continue aligned after `name(`. -/
def callFormat (name : String) (args : List (String × Lean.Json)) : Std.Format :=
  if args.isEmpty then name else
  labeled (Std.Format.text name) "(" (Std.Format.fill
    (Std.Format.joinSep (args.map fun (k, v) => labeled (Std.Format.text k) "=" (renderJson v))
      ("," ++ Std.Format.line))) ++ ")"

/-- A transition label: an action name, or `{name: {param: value, …}}` as `name(param=value, …)`. -/
def actionFormat (j : Lean.Json) : Std.Format := match j with
  | .str s => s
  | .obj kvs => match kvs.toList.find? (·.2 != .null) with
    | some (name, .obj ps) => callFormat name ps.toList
    | some (name, _) => name
    | none => toString j
  | _ => toString j

/-- A value, laid out at `textWidth`. -/
def formatJson (j : Lean.Json) : String := (renderJson j).pretty textWidth

/-- Text, laid out at `textWidth`: a string as it is. -/
def formatText (j : Lean.Json) : String := (renderText j).pretty textWidth

/-- `key = value` at `indent`, with the value's continuation lines aligned after `key = `. -/
def formatField (indent key : String) (j : Lean.Json) : String :=
  (labeled (Std.Format.text (indent ++ key)) " = " (renderJson j)).pretty textWidth

/-- The fields of a JSON object, one `key = value` line each at `indent`, in key order. With
`asText`, the values are text (e.g. type names) rather than values. -/
def formatFields (j : Lean.Json) (indent : String) (asText := false) : String := match j with
  | .obj kvs => "\n".intercalate (if asText
    then kvs.toList.map fun (k, v) => s!"{indent}{k} = {formatText v}"
    else kvs.toList.map fun (k, v) => formatField indent k v)
  | _ => formatJson j

/-- `lead`, a transition label and `trail` on one line; long parameters continue aligned after the
action's `(`. -/
def formatAction (lead : String) (j : Lean.Json) (trail : String := "") : String :=
  (Std.Format.text lead ++ Std.Format.nest lead.length (actionFormat j) ++ trail).pretty textWidth

end Veil.ValueDisplay

namespace Veil

/-! ## `Display`: the JSON shown for a value

Traces and counterexamples show the `Display` of their states, theories and labels, rather than
their `ToJson`, which stays a serialization protocol.

A *structured* instance builds the JSON from the parts of a value and shows each part by its own
`Display`, so that the text output and the widget can use the parts. There are three groups:
- the instances below: numbers and booleans as such, `List` and `Array` as JSON arrays, and a
  subtype as its value;
- the containers, as the tagged sets, maps and multisets above, each next to its `ToJson` instance;
- the state, theory and labels of a module, as JSON objects of their fields or arguments, generated
  by `veil_deriving Display` and `deriving Display`.

Every other type shows its `Repr` as a string (`displayOfRepr`). So, unlike with core `ToJson`,
`some a` and `a` look different, a tuple does not look like a list, and a string is quoted. -/

/-- The JSON that traces and counterexamples show for a value of `α`. -/
class Display (α : Type u) where
  display : α → Lean.Json

/-- Without a structured instance, a value shows its `Repr`, as a string on one line: the text
output cannot re-wrap it, and a line break would misalign it with the text before it. The priority
is below that of every structured instance, including the `low` ones of finite functions. -/
instance (priority := 10) displayOfRepr [Repr α] : Display α where
  display a := .str ((Std.Format.group (repr a)).pretty 100000)

instance : Display Nat := ⟨Lean.toJson⟩
instance : Display Int := ⟨Lean.toJson⟩
instance : Display Bool := ⟨Lean.toJson⟩
instance : Display (Fin n) := ⟨fun i => Lean.toJson i.val⟩

instance [Display α] : Display (List α) where
  display xs := .arr (xs.toArray.map Display.display)

instance [Display α] : Display (Array α) where
  display xs := .arr (xs.map Display.display)

/-- A subtype displays as its value, e.g. a quorum as the set it is. -/
instance [Display α] {P : α → Prop} : Display (Subtype P) where
  display x := Display.display x.val

end Veil
