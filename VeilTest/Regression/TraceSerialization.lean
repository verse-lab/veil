module

public import Veil
public meta import Veil

open Lean Veil

/-! The text of a trace: values wrap at `ValueDisplay.textWidth` and continue aligned, also in a
long transition label, and the type names of the instantiation are text. -/
/--
info: Instantiation:
  node = Fin 3
State 1 (via decide(b=1,
                    q={0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
                       22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39})):
  big = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
         25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44}
  msg = {response: {dat: 7, ses: 2}}
  seq = [1, 2, 3]
-/
#guard_msgs in
#eval do
  let fields := Json.mkObj [
    ("big", ValueDisplay.setJson (Array.range 45)),
    ("msg", json% {response: {ses: 2, dat: 7}}),
    ("seq", toJson [1, 2, 3])]
  let label := json% {decide: {q: $(ValueDisplay.setJson (Array.range 40)), b: 1}}
  let j := Json.mkObj [
    ("instantiation", Json.mkObj [("node", Json.str "Fin 3")]),
    ("states", Json.arr #[Json.mkObj [("index", toJson (1 : Nat)), ("transition", label),
      ("fields", fields)]])]
  IO.println (Veil.TraceDisplay.formatTrace j (ind := ""))

/-! Results that the commands below do not produce, and transition labels or state fields of an
unexpected shape. -/
/--
info: 💥 Error: the checker crashed
Unknown: weird
⚠️ Cancelled
⚠️ Cancelled
Seed: 2
❌ Violation: deadlock
  State 1 (via mk):
    x = 1
  State 1 (via {"a": null}):
null
  State 1 (via 5):
-/
#guard_msgs in
#eval show IO Unit from do
  let state (t fields : Json) : Json :=
    Json.mkObj [("index", toJson (1 : Nat)), ("transition", t), ("fields", fields)]
  let tr := Json.mkObj [("states", Json.arr #[
    state (json% {mk: [1, 2]}) (json% {x: 1}),
    state (json% {a: null}) Json.null,
    state (toJson (5 : Nat)) (Json.mkObj [])])]
  for (kind, j) in [
      (Veil.TraceDisplay.ResultKind.modelCheck, json% {result: "weird", error: "the checker crashed"}),
      (.modelCheck, json% {result: "weird"}),
      (.modelCheck, json% {result: "cancelled"}),
      (.simulate, json% {result: "cancelled", seed: 2}),
      (.modelCheck, Json.mkObj [("result", "found_violation"),
        ("violation", json% {kind: "deadlock"}), ("trace", tr)])] do
    IO.println (← (Veil.TraceDisplay.formatResult kind j).toString)

/-! An infinite domain keeps the stored entries, as a tagged map, instead of enumerating the
function. -/
veil module NonEnumerableTraceField
function stored : Nat → Nat
#gen_state

run_cmd do
  let field : FieldConcreteType State.Label.stored :=
    .concrete (Std.ExtTreeMap.empty.insert 7 11)
  let displayed := toJson field
  unless displayed == json% {"$veil": "map", entries: [{key: 7, value: 11}]} do
    throwError "non-enumerable field lost its stored key/value: {displayed}"

end NonEnumerableTraceField

/-! The trace JSON that the model checker and `#simulate` generate, interpreted and compiled. The
same message appears as an individual, a client map value and a queue item; node keys are tagged
values, and a field of two arguments has tuple keys. -/
veil module TraceSerialization

type client

@[veil_decl]
inductive Node (client : Type) where
  | cloud
  | client (id : client)
deriving instance Veil.Enumeration, Veil.FinEncodable for Node

@[veil_decl]
inductive Msg (client : Type) where
  | request (dat : Nat) (orig : client)
  | response (dat ses : Nat)

immutable individual oneClient : client
function chan : Node client → fQueue (Msg client)
function inbox : client → Option (Msg client)
individual message : Option (Msg client)
function pc : Node client → String
function history : client → List Nat
function count : Node client → client → Nat
relation pending : Node client → Node client → Bool
individual bag : TMapMultiset Nat

veil_set_field_representation function Veil.ArrayAsFinmap
veil_set_field_representation relation Veil.ArrayAsFinset

after_init {
  chan N := fQueue.empty
  chan (.client oneClient) := fQueue.empty.enqueue (.response 7 2)
  inbox C := some (.response 7 2)
  message := some (.response 7 2)
  pc N := "CW"
  pc .cloud := "D"
  history C := [0, 7]
  count N C := 7
  pending M N := false
  pending .cloud (.client oneClient) := true
  bag := TMultiset.insert 2 (TMultiset.insert 2 TMultiset.empty)
}

action clear { message := none }

invariant [diagnostic] false
#gen_spec

-- The same trace, from the interpreted and the compiled checker, and from `#simulate`.
/--
error: ❌ Violation: safety_failure (violates: diagnostic)
  Theory:
    oneClient = 0
  State 0 (via init):
    bag = {2 × 2}
    chan = {cloud ↦ [], {client: {id: 0}} ↦ [{response: {dat: 7, ses: 2}}]}
    count = {[cloud, 0] ↦ 7, [{client: {id: 0}}, 0] ↦ 7}
    history = {0 ↦ [0, 7]}
    inbox = {0 ↦ {response: {dat: 7, ses: 2}}}
    message = {response: {dat: 7, ses: 2}}
    pc = {cloud ↦ D, {client: {id: 0}} ↦ CW}
    pending = {[cloud, {client: {id: 0}}]}
-/
#guard_msgs in
#model_check interpreted { client := Fin 1 } { oneClient := 0 }

/--
error: ❌ Violation: safety_failure (violates: diagnostic)
  Theory:
    oneClient = 0
  State 0 (via init):
    bag = {2 × 2}
    chan = {cloud ↦ [], {client: {id: 0}} ↦ [{response: {dat: 7, ses: 2}}]}
    count = {[cloud, 0] ↦ 7, [{client: {id: 0}}, 0] ↦ 7}
    history = {0 ↦ [0, 7]}
    inbox = {0 ↦ {response: {dat: 7, ses: 2}}}
    message = {response: {dat: 7, ses: 2}}
    pc = {cloud ↦ D, {client: {id: 0}} ↦ CW}
    pending = {[cloud, {client: {id: 0}}]}
-/
#guard_msgs in
#model_check compiled { client := Fin 1 } { oneClient := 0 }

/--
error: ❌ Violation: safety_failure (violates: diagnostic)
  Theory:
    oneClient = 0
  State 0 (via init):
    bag = {2 × 2}
    chan = {cloud ↦ [], {client: {id: 0}} ↦ [{response: {dat: 7, ses: 2}}]}
    count = {[cloud, 0] ↦ 7, [{client: {id: 0}}, 0] ↦ 7}
    history = {0 ↦ [0, 7]}
    inbox = {0 ↦ {response: {dat: 7, ses: 2}}}
    message = {response: {dat: 7, ses: 2}}
    pc = {cloud ↦ D, {client: {id: 0}} ↦ CW}
    pending = {[cloud, {client: {id: 0}}]}
Seed: 1
-/
#guard_msgs in
#simulate interpreted { client := Fin 1 } { oneClient := 0 }
  (numTraces := 1) (maxSteps := 1) (seed := 1)

/--
error: ❌ Violation: safety_failure (violates: diagnostic)
  Theory:
    oneClient = 0
  State 0 (via init):
    bag = {2 × 2}
    chan = {cloud ↦ [], {client: {id: 0}} ↦ [{response: {dat: 7, ses: 2}}]}
    count = {[cloud, 0] ↦ 7, [{client: {id: 0}}, 0] ↦ 7}
    history = {0 ↦ [0, 7]}
    inbox = {0 ↦ {response: {dat: 7, ses: 2}}}
    message = {response: {dat: 7, ses: 2}}
    pc = {cloud ↦ D, {client: {id: 0}} ↦ CW}
    pending = {[cloud, {client: {id: 0}}]}
Seed: 1
-/
#guard_msgs in
#simulate compiled { client := Fin 1 } { oneClient := 0 }
  (numTraces := 1) (maxSteps := 1) (seed := 1)

end TraceSerialization

/-! A satisfying trace shows how the sorts were instantiated; the type names are text. -/
veil module SatTraceInstantiation

type node
relation visited : node → Bool

after_init {
  visited N := false
}

action visit (n : node) {
  visited n := true
}

invariant true

#gen_spec

/--
info: ✅ Satisfying trace found
  Instantiation:
    node = Fin 1
  State 0 (via init):
    visited = {}
  State 1 (via visit(n=0)):
    visited = {0}
-/
#guard_msgs in
sat trace {
  visit
  assert (∃ n, visited n)
}

end SatTraceInstantiation
