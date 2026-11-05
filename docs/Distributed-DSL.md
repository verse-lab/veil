# Distributed Programs

Veil's main DSL describes a system as a set of global actions over a shared
state. For message-passing protocols there is a more compact way: describe the
**program each node runs**, and the **network** that connects the nodes. Veil
compiles such a description into an ordinary Veil module, so `#model_check`,
`#check_invariants`, `sat trace` and the rest work on it unchanged.

```
node program + network assumptions ──compile──▶ Veil module ──▶ model checking / verification
```

The compiled module is strict by construction: a node can only read and write
its own variables, and can only learn about other nodes through messages.

## Example

Leader election in a unidirectional ring (compare with the global-action
version in [Examples/Tutorial/Ring.lean](../Examples/Tutorial/Ring.lean)):

```lean
veil module Ring

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node
open Between TotalOrder

network (synchrony := async)

message token (id : node)

var leader : Bool := false

program (self : node) {
  let nxt :| ∀ z, self ≠ nxt ∧ ((z ≠ self ∧ z ≠ nxt) → btw self nxt z)
  send (token self) to nxt
  repeat
    recv (token id)
    if id = self then
      leader := true
    else if le self id then
      let nxt :| ∀ z, self ≠ nxt ∧ ((z ≠ self ∧ z ≠ nxt) → btw self nxt z)
      send (token id) to nxt
}

safety [single_leader] leader L1 ∧ leader L2 → L1 = L2
invariant [leader_greatest] leader L → le N L
invariant [receive_self_msg_only_if_greatest] token_net S L L → le N L
invariant [no_bypass] token_net P D S ∧ btw S N D → le N S

#gen_spec
#model_check { node := Fin 4 } { }
#check_invariants

end Ring
```

Properties are stated over the *global* state: a node variable `leader : Bool`
is the field `leader : node → Bool`, and the network is visible through
generated fields such as `token_net` (see [The generated module](#the-generated-module)).

## Declarations

The declarations come in this order: the module's types, theory and any extra
state, then `network`, `message`s and `var`s, then `program`, then properties
and verification commands. `program` generates the module's state, initial
state and actions, so it comes after every state declaration and replaces
`#gen_state` and `after_init`.

### `network`

```lean
network (synchrony := async) (loss := reliable) (channels := set)
        (order := unordered) (faults := none) (complexity := false)
```

Every option is optional; the defaults are shown above.

| Option | Values | Meaning |
|---|---|---|
| `synchrony` | `async` | Nodes take steps in any interleaving, and a message can be delivered at any time after it is sent. |
| | `sync` | Lock-step rounds: in each round every running node takes one step, then all messages of the round are delivered together. |
| `loss` | `reliable` | Messages are never lost. |
| | `lossy` | The network may drop any message (`async`), or any subset of a round's messages (`sync`). |
| `channels` | `set` | Identical messages in flight (same sender, receiver and content) are merged. This keeps the state finite and the verification conditions free of arithmetic. |
| | `multiset` | Every copy is kept (`async` only). |
| `order` | `unordered` | Messages in flight may be received in any order. |
| | `fifo` | Each channel (sender to receiver) delivers messages in the order they were sent (`async` only; see [Ordering](#ordering)). |
| `faults` | `none` | All nodes follow the program. |
| | `crash`, `crash f` | Nodes may crash, at most `f` of them (any term, e.g. an `immutable individual` declared before `network`). See [Faults](#faults). |
| | `byzantine`, `byzantine p` | The nodes satisfying `p` are Byzantine. Without `p`, the compiler declares a theory relation `byz : node → Bool`, given in the second argument of `#model_check`. |
| `complexity` | `false`/`true` | Count messages: `net_msgs` (sent with `send`), `net_bcasts` (sent with `broadcast`) and, for `sync`, `net_rounds`. |

`network` also enables the rest of the syntax on this page. Its keywords
(`send`, `recv`, `to`, ...) are reserved only in modules that declare a network.

For safety properties of an asynchronous system, loss usually makes no
difference: a message that is never delivered is already a possible behaviour.
It matters for termination (see the `termination` clause in the
[Model Checker Guide](ModelChecker-Guide.md#deadlocks-and-termination)), and in
synchronous networks, where delivery within the round is otherwise guaranteed.

### `message`

```lean
message vote (r : round) (v : value)
message ack
```

Declares a message kind and the types of its fields. A message also carries its
sender, which the network fills in: nodes cannot forge it.

Field types must be finite (an uninterpreted `type`, an `enum`, `Bool`,
`Fin n`, ...), because receiving a message is an action parameterised by its
fields, and the model checker enumerates action parameters.

### `var`

```lean
var leader : Bool := false
var heard : node → Bool := fun _ => false
var input : value := *
var best : node := self
```

A variable every node has its own copy of. The initial value may refer to the
node as `self`, or be `*` (an arbitrary value, chosen independently for each
node). Without an initial value, the variable starts at its type's default.

### `program`

```lean
program (self : node) {
  ...
}
```

The program every node runs, with `self` the node running it. Its body is a
Veil action body (`require`, `let x :| P`, `if`, assignments, ...) extended
with the statements below. Different roles are written with `if`, e.g.
`if self = coordinator then ... else ...`.

## Statements

| Statement | Meaning |
|---|---|
| `send (m a b) to dst` | Send message `m a b` to `dst`. |
| `broadcast (m a b)` | Send it to every node, **including `self`**. |
| `recv (m x y) from src` | Block until a message `m` arrives, then bind its fields and sender. `from src` is optional. |
| `recv`<br>`\| (m x) from s => ...`<br>`\| (n y) => ...` | Block until one of several kinds of message arrives, and run the matching alternative. |
| `next_round` | (`sync` only) End this node's step in the current round. |
| `received (m a b) from src` | (`sync` only) A proposition: this node received `m a b` from `src` in the previous round. Without `from`, from some node. |
| `halt` | Stop the node. Reaching the end of the program does the same. |
| `while c do ...`, `repeat ...` | Loops. |

In a `recv` pattern, a field written as a variable binds it, and a field
written as any other term (e.g. `true`, an `enum` value, `r + 1`) only
matches messages with that value. As in Lean's patterns, an identifier that
names a constructor is a value, not a variable:

```lean
recv
| (vote true) from p => heard p := true
| (vote false) from _p => aborted := true
```

`send`, `recv` and the other statements may appear at the top level of the
program and inside `if`, `while`, `repeat` and `recv` alternatives, but not
inside `match` or nested `do` blocks. `for`, `break` and `continue` are not
supported.

## Semantics

A node runs until it **blocks**: at a `recv`, at `next_round`, or when it
halts. Everything a node does between two blocking points is one **atomic
step**. Loop heads are step boundaries too, so a loop that never blocks still
progresses one iteration per step rather than running forever inside one.

* In an `async` network, any node that can take a step may do so, in any
  order. A node blocked at a `recv` can take a step when a matching message is
  in flight, and receiving removes that message. A `require` that does not hold
  blocks the node.
* In a `sync` network, each round lets every node that has not halted take one
  step, ending at its next `next_round` (or `halt`). Once all have done so, all
  messages sent in the round are delivered at once, and become visible through
  `received` until the end of the next round.

### Faults

* **Crash** (`faults := crash f`). At any time, the network may stop a node
  that is still running, at most `f` times. A crashed node takes no more
  steps; its `pc` is `pc_crashed`, and the generated `crashed n` holds. In an
  `async` network, the messages it sent before crashing stay in flight. In a
  `sync` network, a node that crashes during a round may have sent any subset
  of that round's messages: each of them may be dropped before the round ends.
  This is the usual model of FloodSet-style protocols.
* **Byzantine** (`faults := byzantine p`). The nodes satisfying `p` do not run
  the program. Instead, at any time, they may send any message to any node,
  with their own identity as the sender (channels are authenticated). The
  predicate is part of the theory: in a model check, you choose which nodes are
  faulty, e.g. `{ byz := fun n => n = 2 }`; for SMT proofs, state what you
  assume about it, for instance with Veil's `ByzNodeSet`:

  ```lean
  instantiate bns : ByzNodeSet node nset
  open ByzNodeSet
  network (faults := byzantine is_byz)
  ```

  Node programs cannot mention the predicate: nodes do not know who is faulty.

Either way, the generated ghost relation `correct n` holds for the nodes that
follow the program, so properties are usually stated over correct nodes:

```lean
safety [agreement] correct A ∧ correct B ∧ decided A ∧ decided B → decision A = decision B
```

### Ordering

With `order := fifo`, every message carries a sequence number. The compiler
declares a sort `net_seq` with `instantiate net_seq_order : TotalOrderWithMinimum
net_seq`. Each channel keeps the number of the next message to send
(`net_seq_sent src dst`) and the next one to receive (`net_seq_recv src dst`),
and a `recv` can only take the next message of a channel. If that message does
not match any alternative, the node waits, even if a matching message is
queued behind it (head-of-line blocking). With `loss := lossy`, a `recv` may
take any later message instead, and the ones it skips are lost; the messages
that do arrive still arrive in order.

Sequence numbers are an uninterpreted, totally ordered sort, so SMT proofs
need no arithmetic. When model checking, instantiate it with a finite type,
e.g. `{ node := Fin 2, net_seq := Fin 4 }`: sending a message needs a next
sequence number, so this allows at most 3 messages per channel, and a node
that would send a 4th blocks.

### Bindings do not survive blocking

`let` bindings live only until the node blocks. A value that must survive a
`recv`, `next_round` or a loop iteration belongs in a `var`:

```lean
program (self : node) {
  let y := f self
  recv ping
  x := y   -- error: `y` is not available here ...
}
```

The compiler reports every use of an expired binding.

### Locality

Inside `program`, every mention of a node variable `x` means `x self`, this
node's copy. There is no way to name another node's copy, and the program may
not mention any other mutable state: not the network's state, nor mutable state
declared outside the program. Immutable state (the background theory, e.g.
`TotalOrder` or a topology) is shared knowledge and may be read freely.

## The generated module

`program` generates the following, which properties, `sat trace` queries and
counterexample traces refer to. To see the generated commands, write `#desugar_program` directly after the
`program`: like `exact?`, it offers a suggestion that replaces the `program`
with the plain Veil it compiles to.

| Name | Kind | Meaning |
|---|---|---|
| `pc : node → pc_label` | state | Where each node is suspended. |
| `pc_start`, `pc_done` | `pc_label` | Not started yet; halted. |
| `pc_recv<k>`, `pc_round<k>`, `pc_loop<k>` | `pc_label` | Blocked at the `k`-th `recv` or `next_round`, or at the head of the `k`-th loop. |
| `x : node → T` | state | Node variable `x : T` (a `relation` if `T` returns `Bool`). |
| `m_net : node → node → T₁ → … → Bool` | state | (`async`) Messages `m` in flight, by sender and receiver. `→ Nat` (a count) with `channels := multiset`; with `order := fifo`, a `net_seq` argument follows the receiver. |
| `m_out`, `m_in` | state | (`sync`) Messages `m` sent in the current round; delivered at the end of the previous one. |
| `net_ready : node → Bool` | state | (`sync`) The node has not yet taken its step in this round. |
| `net_msgs`, `net_bcasts`, `net_rounds` | state | (`complexity := true`) Message and round counts. |
| `pc_crashed`, `net_crashes`, `net_crashing n` | `pc_label`, state | (`crash`) A crashed node; the number of crashes; `n` crashed in the current round (`sync`). |
| `byz : node → Bool` | theory | (`byzantine` without a predicate) The Byzantine nodes. |
| `net_seq`, `net_seq_order` | sort, instance | (`fifo`) Sequence numbers and their order. |
| `net_seq_sent`, `net_seq_recv : node → node → net_seq` | state | (`fifo`) Next number to send, and to receive, on each channel. |
| `halted n` | ghost | `pc n = pc_done`. |
| `correct n` | ghost | `n` follows the program: not crashed (`crash`), not Byzantine (`byzantine`); `True` otherwise. |
| `crashed n` | ghost | (`crash`) `pc n = pc_crashed`. |
| `net_empty` | ghost | No message is in flight (`async`), or none has been sent in this round (`sync`). |
| `node_start self` | action | The node's first step. |
| `node_recv<k>_<m> self src fields…` | action | Receive `m` at the `k`-th `recv`, and run until the next blocking point. |
| `node_round<k> self`, `node_loop<k> self` | action | Resume after the `k`-th `next_round`, or at the head of the `k`-th loop. |
| `net_drop_<m> src dst fields…` | action | (`lossy`) Lose a message in flight (`async`) or of the current round (`sync`); (`sync`, `crash`) lose a message of a node that crashed in this round. |
| `net_byz_send_<m> src dst fields…` | action | (`byzantine`) A Byzantine node sends a message. |
| `net_crash n` | action | (`crash`) Node `n` crashes. |
| `net_next_round` | action | (`sync`) End the round and deliver its messages. |

You may add further actions (e.g. failures, or an adversary) after `program`.
They are ordinary Veil actions, and may use the generated state.

## Limitations

* One program per module. Roles are written with `if`.
* No partial synchrony and no duplicating networks yet. They, and other fault
  models, can be written as extra actions after `program`.
* Byzantine nodes branch on every message they can send, at every step, so
  model check small instances. With `channels := multiset`, they can also make
  the state space infinite.
* Message fields must have finite types.
* Unbounded `Nat` variables or counters make the state space infinite unless
  the program terminates; bound the search with a `state_constraint` if needed.
* `program` owns the module's initial state: mutable state declared outside it
  starts at its default value.
