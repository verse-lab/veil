module

public import Lean.Data.Json.FromToJson.Basic

@[expose] public section

/-! # Display of values

How Veil displays the values of states, theories, transitions and picks, in the text output of
traces and counterexamples and in the widget: the `Display` class, the `Repr` and JSON helpers of
the concrete containers, the tags of sets, maps and multisets in JSON, and the rendering of JSON as
text. The containers pass their logical contents (members, entries, multiplicities) rather than
their storage.

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
  violation kinds, property names, error messages, the seed and type names. Type names are text
  here because they arrive as printed type expressions.

Both show strings as they are, but keeping their roles separate lets the rendering of values change
without touching text. -/

-- NOTE: The following code mostly depends on an implicit contract about the JSON structure
-- of containers, including sets/maps/records etc. Somehow, there should be a way to
-- automatically synthesize the encoders and decoders from the contract, so that we don't
-- have to write `recordJson`/`record?`-like pairs manually.

namespace Veil.ValueDisplay

/-! ## `Repr`: logical contents as Lean text

These take lists, as `Std.Format.joinSep` does. A constructor application is laid out by
`callFormat` below, as an action label is. -/

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

/-! ## JSON: records and constructors

The states and theories of a module are records, and its transition labels are constructors, so
that their fields and arguments keep their declaration order, which a JSON object would sort:
- `{"$veil": "record", "type": "State", "fields": [{"name": "x", "value": v}, …]}`
- `{"$veil": "ctor", "type": "Label", "name": "send", "args": [{"name": "n", "value": v}, …]}`,
  where an argument without a name has only a `"value"`.

`type` is the short name of the declaration. The arguments of a constructor are *named values*, as
are the picks of a trace (`Choice`). -/

def recordJson (type : String) (fields : List (String × Lean.Json)) : Lean.Json :=
  Lean.Json.mkObj [("$veil", .str "record"), ("type", .str type), ("fields", .arr <|
    fields.toArray.map fun (n, v) => Lean.Json.mkObj [("name", .str n), ("value", v)])]

/-- A value with an optional name: `{"name": n, "value": v}`, or `{"value": v}` without a name. -/
def namedValueJson : Option String × Lean.Json → Lean.Json
  | (some n, v) => Lean.Json.mkObj [("name", .str n), ("value", v)]
  | (none, v) => Lean.Json.mkObj [("value", v)]

def ctorJson (type name : String) (args : List (Option String × Lean.Json)) : Lean.Json :=
  Lean.Json.mkObj [("$veil", .str "ctor"), ("type", .str type), ("name", .str name),
    ("args", .arr <| args.toArray.map namedValueJson)]

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

/-- The type and the fields of a record, in declaration order. Only a complete envelope counts. -/
def record? (j : Lean.Json) : Option (String × Array (String × Lean.Json)) := do
  let .obj fs := j | none
  guard (fs.size == 3)
  let .str "record" ← (j.getObjVal? "$veil").toOption | none
  let .str type ← (j.getObjVal? "type").toOption | none
  let .arr entries ← (j.getObjVal? "fields").toOption | none
  let fields ← entries.mapM fun e => do
    let .obj efs := e | none
    guard (efs.size == 2)
    let .str n ← (e.getObjVal? "name").toOption | none
    return (n, ← (e.getObjVal? "value").toOption)
  return (type, fields)

/-- The name, if there is one, and the value of a named value (`namedValueJson`). -/
def namedValue? (j : Lean.Json) : Option (Option String × Lean.Json) := do
  let .obj fs := j | none
  let v ← (j.getObjVal? "value").toOption
  if fs.size == 1 then return (none, v)
  guard (fs.size == 2)
  let .str n ← (j.getObjVal? "name").toOption | none
  return (some n, v)

/-- The type, the name and the arguments of a constructor, in declaration order. Only a complete
envelope counts. -/
def ctor? (j : Lean.Json) : Option (String × String × Array (Option String × Lean.Json)) := do
  let .obj fs := j | none
  guard (fs.size == 4)
  let .str "ctor" ← (j.getObjVal? "$veil").toOption | none
  let .str type ← (j.getObjVal? "type").toOption | none
  let .str name ← (j.getObjVal? "name").toOption | none
  let .arr entries ← (j.getObjVal? "args").toOption | none
  let args ← entries.mapM namedValue?
  return (type, name, args)

/-- The fields of a record in declaration order, or of any other object that is not a tagged value
in key order. -/
def fields? (j : Lean.Json) : Option (Array (String × Lean.Json)) :=
  if let some (_, fields) := record? j then some fields
  else if (collection? j).isSome || (ctor? j).isSome then none
  else match j with
    | .obj kvs => some kvs.toArray
    | _ => none

/-! ## Text output

For `TraceDisplay` and `VerificationResults`. `renderJson`, `renderText`, `callFormat`,
`choiceFormat` and `actionFormat` build a `Std.Format`; `formatJson`, `formatText`, `formatField`,
`formatFields`, `formatAction` and `formatChoices` lay out one value or one line at `textWidth`,
given what precedes it on its line; the callers only assemble these lines into messages. -/

/-- The width of the text output of traces and counterexamples. -/
def textWidth : Nat := 100

/-- `label` and `sep` followed by `value`, whose continuation lines align after `sep`. The label is
measured as laid out on one line, as it is unless it is very long itself. -/
def labeled (label : Std.Format) (sep : String) (value : Std.Format) : Std.Format :=
  let lead := label ++ sep
  lead ++ Std.Format.nest (lead.pretty 100000).length value

/-- `name(k=v, …)`, as action labels and constructor applications (`deriving ConstructorRepr`) are
shown: `v` alone for an argument without a name, and `name` alone without arguments. Arguments fill
each line and continue aligned after `name(`. A call reads as one unit, so it needs no parentheses
as an argument. -/
def callFormat (name : String) (args : List (Option String × Std.Format)) : Std.Format :=
  if args.isEmpty then name else
  labeled (Std.Format.text name) "(" (Std.Format.fill
    (Std.Format.joinSep (args.map fun
      | (some k, v) => labeled (Std.Format.text k) "=" v
      | (none, v) => v)
      ("," ++ Std.Format.line))) ++ ")"

/-- `name = v`, or `v` alone without a name: a pick as traces show it (`Choice`). -/
def choiceFormat : Option String × Std.Format → Std.Format
  | (some n, v) => labeled (Std.Format.text n) " = " v
  | (none, v) => v

/-- A JSON value as traces and counterexamples show it: tagged containers in set notation (`{a, b}`,
`{k ↦ v}`, `{a × n}`), arrays in brackets, records as `{k: v}` in declaration order and other
objects in key order, constructors as `name(k=v, …)`, strings verbatim. Elements fill each line,
and continue aligned after the opening bracket. -/
partial def renderJson (j : Lean.Json) : Std.Format :=
  if let some fields := fields? j then
    seq "{" (fields.toList.map fun (k, v) => labeled (Std.Format.text k) ": " (renderJson v)) "}"
  else if let some (_, name, args) := ctor? j then
    callFormat name (args.toList.map fun (k, v) => (k, renderJson v))
  else match collection? j with
  | some (kind, entries) =>
    let entry (e : Lean.Json) : Std.Format :=
      if kind == "map" then labeled (renderJson (e.getObjValD "key")) " ↦ " (renderJson (e.getObjValD "value"))
      else if kind == "multiset" then
        renderJson (e.getObjValD "element") ++ " × " ++ renderJson (e.getObjValD "count")
      else renderJson e
    seq "{" (entries.toList.map entry) "}"
  | none => match j with
    | .arr elems => seq "[" (elems.toList.map renderJson) "]"
    | .str s => s
    | _ => j.compress
where
  seq (l : String) (parts : List Std.Format) (r : String) : Std.Format :=
    Std.Format.bracketFill l (Std.Format.joinSep parts ("," ++ Std.Format.line)) r

/-- Text rather than a value: a string shows as it is, and anything else as a value. Result tags,
property names, error messages and type names are text. -/
def renderText (j : Lean.Json) : Std.Format := match j with
  | .str s => s
  | _ => renderJson j

/-- A transition label: a constructor as `name(param=value, …)`, or an action name. An object
`{name: {param: value, …}}` reads as a constructor with its parameters in key order. -/
def actionFormat (j : Lean.Json) : Std.Format :=
  if let some (_, name, args) := ctor? j then
    callFormat name (args.toList.map fun (k, v) => (k, renderJson v)) else
  match j with
  | .str s => s
  | .obj kvs => match kvs.toList.find? (·.2 != .null) with
    | some (name, .obj ps) => callFormat name (ps.toList.map fun (k, v) => (some k, renderJson v))
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

/-- The fields of a record or another object (`fields?`), one `key = value` line each at `indent`.
With `asText`, the values are text (e.g. type names) rather than values. -/
def formatFields (j : Lean.Json) (indent : String) (asText := false) : String :=
  match fields? j with
  | some fields => "\n".intercalate (if asText
    then fields.toList.map fun (k, v) => s!"{indent}{k} = {formatText v}"
    else fields.toList.map fun (k, v) => formatField indent k v)
  | none => formatJson j

/-- `lead`, a transition label and `trail` on one line; long parameters continue aligned after the
action's `(`. -/
def formatAction (lead : String) (j : Lean.Json) (trail : String := "") : String :=
  (Std.Format.text lead ++ Std.Format.nest lead.length (actionFormat j) ++ trail).pretty textWidth

-- CHECK Might share the same flow with some other function?
/-- `choices: x = v, …` at `indent`: the picks that led to a state, each a named value, or text if
it is not one. The picks fill each line, and continue aligned after `choices: `. -/
def formatChoices (indent : String) (choices : Array Lean.Json) : String :=
  (labeled (Std.Format.text (indent ++ "choices")) ": " (Std.Format.fill (Std.Format.joinSep
    (choices.toList.map fun c => match namedValue? c with
      | some (n, v) => choiceFormat (n, renderJson v)
      | none => renderText c)
    ("," ++ Std.Format.line)))).pretty textWidth

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
- the state, theory and labels of a module, as the records and constructors above, with their fields
  and arguments in declaration order, generated by `veil_deriving Display` and `deriving Display`.

Every other type shows its `Repr` as a string (`displayOfRepr`). So, unlike with core `ToJson`,
`some a` and `a` look different, a tuple does not look like a list, and a string is quoted. -/

/-- The JSON that traces and counterexamples show for a value of `α`. -/
class Display (α : Type u) where
  display : α → Lean.Json

/-- `f` laid out on one line. Use `@[noinline]` here so the model checker can skip formatting
candidates when `LogSwitch` is off. -/
@[noinline] def ValueDisplay.oneLine (f : Std.Format) : String :=
  (Std.Format.group f).pretty 100000

/-- Without a structured instance, a value shows its `Repr`, as a string on one line: the text
output cannot re-wrap it, and a line break would misalign it with the text before it. The priority
is below that of every structured instance, including the `low` ones of finite functions. -/
instance (priority := 10) displayOfRepr [Repr α] : Display α where
  display a := .str (ValueDisplay.oneLine (repr a))

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

/-- `Repr`, under a name to derive: `deriving ConstructorRepr` declares the `Repr` of an inductive
type that shows its values as action labels are shown, by the bare names of their constructors
(`ValueDisplay.callFormat`), e.g. `response(dat=7, ses=2)`. A structure, or a recursive or indexed
type, gets the derived `Repr` instead. `@[veil_decl]` types and enums derive it. -/
abbrev ConstructorRepr (α : Type u) : Type u := Repr α

/-! ## Picks -/

/-- A pick in the log of an execution: the candidate, as its `Display` shows it, and the name of
what the pick is bound to, if it has one. A trace shows the picks that led to each state as its
`"choices"`, each a named value (`ValueDisplay.namedValueJson`). -/
structure Choice where
  name : Option String := none
  value : Lean.Json
deriving Inhabited

instance : Lean.ToJson Choice := ⟨fun c => ValueDisplay.namedValueJson (c.name, c.value)⟩

/-- `name = value`, as traces show a pick. -/
instance : Repr Choice where
  reprPrec c _ := ValueDisplay.choiceFormat (c.name, ValueDisplay.renderJson c.value)

instance : ToString Choice := ⟨fun c => (repr c).pretty ValueDisplay.textWidth⟩

end Veil
