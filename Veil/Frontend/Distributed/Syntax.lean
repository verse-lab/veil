module

public meta import Lean
public meta import Lean.Parser

public meta section

open Lean Parser

/-! # Syntax of the distributed-program frontend

A distributed system is described by the program every node runs, plus the
assumptions about the network that connects the nodes. See
`docs/Distributed-DSL.md` for the language and its translation into an
ordinary Veil module.

Only `network` lives in the `Veil` namespace, so it is available in every
`veil module`. The rest of the syntax (`message`, `var`, `program`, and the
statements `send`, `recv`, ...) is scoped to `Veil.Distributed`, which the
`network` command opens. Its keywords (e.g. `send`, `recv`, `to`) are then
reserved only in modules that use this frontend, and existing specifications
that name their actions `send`/`recv` are unaffected.
-/

namespace Veil

/-- One network assumption, e.g. `(synchrony := async)` or `(faults := crash f)`. -/
syntax networkOption := "(" ident " := " ident (ppSpace term:max)? ")"

/-- Declare the network the nodes of this module communicate over, and switch
on the distributed-program frontend. Options (defaults first):

- `synchrony := async | sync`: asynchronous interleaving, or lock-step rounds
- `loss := reliable | lossy`: whether the network may drop messages
- `channels := set | multiset`: whether identical in-flight messages are merged
  (only for `async`; `sync` channels are per-round sets)
- `order := unordered | fifo`: whether each channel delivers messages in the
  order they were sent (only for `async`)
- `faults := none | crash | crash f | byzantine | byzantine p`: nodes may crash
  (at most `f` of them), or the nodes satisfying `p` (by default, a generated
  theory relation `byz`) are Byzantine
- `complexity := false | true`: count messages sent (and rounds, for `sync`)

Example:
```lean
network (synchrony := async) (loss := lossy) (faults := crash f)
```
-/
scoped syntax (name := networkDeclaration) "network" networkOption* : command

end Veil

namespace Veil.Distributed

/-- A message pattern `(kind x y) from src` (the `from` part is optional). -/
syntax messagePattern := term:max (" from " ident)?

/-- The initial value of a node variable: a term, or `*` for an arbitrary one. -/
syntax varInit := " := " ("*" <|> term)

/-- Declare a message kind and the types of its fields, e.g.
`message vote (r : round) (v : value)`. -/
scoped syntax (name := messageDeclaration) "message " ident bracketedBinder* : command

/-- Declare a variable that every node has its own copy of, e.g.
`var leader : Bool := false`. The initial value may refer to the node as
`self`, and may be `*` (arbitrary). -/
scoped syntax (name := varDeclaration) "var " ident " : " term (varInit)? : command

/-- The program every node runs. `self` names the node running it. -/
scoped syntax (name := programDeclaration)
  "program " "(" ident " : " term ")" " {" doSeq "}" : command

/-- Send a message: `send (vote r v) to dst`. -/
scoped syntax (name := sendDo) "send " term:max " to " term : doElem

/-- Send a message to every node, including the sender itself.

With a guard on the same line, the message's fields may be pattern variables
(capitalised, as in Veil assignments), and every instance satisfying the guard
is sent: `broadcast (est V) if W V` sends `est v` for every `v` with `W v`. -/
scoped syntax (name := broadcastDo)
  withPosition("broadcast " term:max (lineEq " if " term)?) : doElem

/-- Block until a message matching the pattern arrives (asynchronous networks
only): `recv (vote r v) from src`. Fields given as terms rather than names
select which messages can be received. -/
scoped syntax (name := recvDo) "recv " messagePattern : doElem

/-- One alternative of a multi-way `recv`. -/
syntax recvArm := "| " messagePattern " => " doSeq

/-- Block until a message matching one of the patterns arrives:
```lean
recv
| (ack r) from src => ...
| (nack r) from src => ...
```
-/
scoped syntax (name := recvArmsDo) "recv" recvArm+ : doElem

/-- Stop this node. Reaching the end of the program has the same effect. -/
scoped syntax (name := haltDo) "halt" : doElem

/-- End this node's part of the current round (synchronous networks only). -/
scoped syntax (name := nextRoundDo) "next_round" : doElem

/-- Whether this node received the message in the previous round
(synchronous networks only): `received (vote r v) from src`, or
`received (vote r v)` for "from some node". -/
scoped syntax (name := receivedTerm) "received " term:max (" from " term:max)? : term

/-- Show the plain Veil commands the preceding `program` compiles to, with a
suggestion that replaces the `program` (and this command) by them. Write it
directly after the `program`. -/
scoped syntax (name := desugarProgramCmd) "#desugar_program" : command

end Veil.Distributed
