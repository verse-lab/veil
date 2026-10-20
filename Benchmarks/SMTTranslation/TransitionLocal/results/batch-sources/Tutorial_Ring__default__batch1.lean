module

public import Veil

set_option Elab.async false
section

open Lean Elab Tactic Meta Veil

meta def symbolicBenchEvent (event phase status : String) (elapsed : Nat := 0)
    (extra : List (String × Json) := []) : CoreM Unit := do
  let j := Json.mkObj ([
    ("event", toJson event), ("phase", toJson phase), ("status", toJson status),
    ("elapsed_ms", toJson elapsed), ("mono_ms", toJson (← IO.monoMsNow))] ++ extra)
  IO.FS.withFile (System.FilePath.mk ((← getOptions).get `symbolicBench.eventPath "")) .append fun h => h.putStrLn j.compress

meta partial def symbolicBenchIntroData (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .forallE _ domain _ _ := target.consumeMData | return goal
  if ← isProp domain then return goal
  let (_, next) ← withOptions (fun opts => opts.setBool `tactic.hygienic false) goal.intro1
  symbolicBenchIntroData next

elab "symbolic_bench_intro_data" : tactic => do
  liftMetaTactic1 fun goal => return some (← symbolicBenchIntroData goal)

elab "symbolic_bench_phase " label:str t:tactic : tactic => do
  if (← getGoals).isEmpty then
    symbolicBenchEvent "stage" label.getString "skipped_goal_closed"
  else
    symbolicBenchEvent "stage" label.getString "begin"
    let start ← IO.monoMsNow
    let hbStart ← IO.getNumHeartbeats
    try
      withoutRecover <| evalTactic t
      symbolicBenchEvent "stage" label.getString "complete" ((← IO.monoMsNow) - start)
        [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    catch ex =>
      symbolicBenchEvent "stage" label.getString "failed" ((← IO.monoMsNow) - start)
        [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
      throw ex

meta def symbolicBenchMetaPhase {α : Type} (label : String) (computation : MetaM α) : MetaM α := do
  symbolicBenchEvent "stage" label "begin"
  let start ← IO.monoMsNow
  let hbStart ← IO.getNumHeartbeats
  try
    let value ← computation
    symbolicBenchEvent "stage" label "complete" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    return value
  catch ex =>
    symbolicBenchEvent "stage" label "failed" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
    throw ex

meta def symbolicBenchTacticPhase {α : Type} (label : String) (computation : TacticM α) : TacticM α := do
  symbolicBenchEvent "stage" label "begin"
  let start ← IO.monoMsNow
  let hbStart ← IO.getNumHeartbeats
  try
    let value ← computation
    symbolicBenchEvent "stage" label "complete" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart))]
    return value
  catch ex =>
    symbolicBenchEvent "stage" label "failed" ((← IO.monoMsNow) - start)
      [("heartbeats", toJson ((← IO.getNumHeartbeats) - hbStart)), ("error", toJson (← ex.toMessageData.toString))]
    throw ex

elab "symbolic_bench_extract " eventPath:str path:str t:tactic : tactic => do
  withOptions (fun opts => opts.set `symbolicBench.eventPath eventPath.getString) do
    symbolicBenchEvent "pipeline" "pipeline" "begin" 0 [
      ("maxHeartbeats", toJson (maxHeartbeats.get (← getOptions))),
      ("maxRecDepth", toJson (maxRecDepth.get (← getOptions)))]
    let start ← IO.monoMsNow
    withoutRecover <| evalTactic t
    symbolicBenchEvent "milestone" "preprocessing" "complete" ((← IO.monoMsNow) - start)
    if (← getGoals).isEmpty then
      symbolicBenchEvent "pipeline" "pipeline" "discharged" ((← IO.monoMsNow) - start)
    else
      Veil.withBackwardsCompatibility <| withMainContext do
        let (mv, hs) ← symbolicBenchTacticPhase "cleanup" do
          let hs := (← getFVarIds (← Veil.getPropsInContext)).map Expr.fvar
          let goal ← getMainGoal
          let mv := (← Meta.mkFreshExprMVar (← goal.getType)).mvarId!
          let mv ← mv.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
          return (mv, hs)
        let mut mv := mv
        let mut hs := hs
        let steps : Array (String × (MVarId → Array Expr → MetaM Smt.Preprocess.Result)) := #[
          ("pushHints", Smt.Preprocess.pushHintsToCtx),
          ("smt-intros", Smt.Preprocess.intros),
          ("negateGoal", Smt.Preprocess.negateGoal),
          ("normalize", Smt.Preprocess.normalize),
          ("embedding", Smt.Preprocess.embeddingWithConfig { embedBool := false })]
        for (label, step) in steps do
          let result ← symbolicBenchMetaPhase label <| mv.withContext <| step mv hs
          mv := result.mv
          hs := result.hs
        let cmds ← symbolicBenchMetaPhase "translate" <| mv.withContext do
          let (fvNames, _) ← Smt.genUniqueFVarNames
          Smt.prepareSmtQuery hs.toList fvNames
        let query ← symbolicBenchMetaPhase "serialize" do
          let query := Smt.Translate.Command.cmdsAsQuery (.setLogic "ALL" :: cmds ++ [.checkSat])
          IO.FS.writeFile path.getString query
          return query
        symbolicBenchEvent "pipeline" "pipeline" "complete" ((← IO.monoMsNow) - start)
          [("bytes", toJson query.utf8ByteSize), ("commands", toJson cmds.length)]
    -- Deliberately abandon the measurement declaration; no theorem is admitted.
    throwError "SYMBOLIC_BMC_EXTRACTION_COMPLETE: query extraction only; no proof claimed"

end

-- This makes the Veil DSL available in this file, and imports the Veil
-- standard library (`Veil.Std`), which contains a number of useful
-- first-order-logic axiomatisations of common structures.

/-! # Leader Election in a Ring

This file specifies a very simple distributed protocol in Veil, showcasing the
framework's main features.

The protocol is leader election in a ring. It works as follows:

- There are a finite number of nodes, each of which has a unique identifier.
- The nodes are arranged in a ring topology, where each node has a unique
  successor and predecessor. Nodes can only send messages to their immediate
  successor. (That is, the ring is unidirectional.)
- The goal is for one node to be elected as leader.
- Every node sends a message containing its identifier to its successor.
- When a node receives a message, it only forwards it along the ring if the
  contained identifier is GREATER than its own.
- A node becomes the leader if it receives its own identifier from its
  predecessor.

The protocol works because only the node with the highest identifier can
circulate its message around the entire ring. Each node forwards messages
containing higher identifiers than its own. Since identifiers are unique, the
maximum identifier will eventually return to its originating node, which becomes
the leader. All other identifiers get blocked by nodes with higher identifiers
during their traversal.

Concretely, the protocol has the following _safety_ property: at most one node
can be elected as leader.

In the remainder of this file, we will specify the protocol in Veil, test it
using Veil's explicit-state model checker, and prove its correctness
automatically using SMT.
-/

/- This defines a new Veil module named `Ring`. In Lean terms, `Ring` is a
`namespace` in which Veil's module DSL is available. -/
veil module Ring

/- This defines a new (uninterpreted) type `node`, to represent node IDs. The
`type` command in Veil defines a type parameter of the module, together with
`DecidableEq` and `Nonempty`/`Inhabited` instances, which make it sound to use
as an SMT sort and possible to execute. When verifying, Veil universally
quantifies over `node`, i.e. it proves the protocol correct for _all_ types
`node`; when model checking, we provide a concrete instantiation (e.g.
`Fin 4`). -/
type node

/- This instantiates the `TotalOrder` class for `node`. You can right-click and
'Go to definition' (F12) to see the axioms this introduces.

Concretely, it defines an (immutable) relation `tot.le` between nodes, and
provides the standard reflexivity, transitivity, antisymmetry, and totality
axioms for it. -/
instantiate tot : TotalOrder node

/- This instantiates the `Between` class for `node`. It encodes the fact that
the `node`s form a (unidirectional) ring topology.

It defines an (immutable) relation `btwn.btw (x y z : node)` between nodes, read
as "y is between x and z".

An illustration of a ring, going clockwise:

    .---.---.
   /         \
  w           x      in this illustration, the ring goes clockwise
  |           |      (i.e. w -> x -> y -> z -> w)
  z           .
   \         /
    .---.---y

The relation `btw x y z` means that `y` lies between `x` and `z`, as
shown in the diagram above.

The axioms are as follows:
- [btw_ring] `∀ x y z, btw x y z → btw y z x`
- [btw_trans] `∀ w x y z, btw w x y → btw w y z → btw w x z`
- [btw_side] `∀ w x y, btw w x y → ¬ btw w y x`
  - this encodes the fact that the ring is unidirectional: in our
  example diagram, it is NOT the case that `y` is between `w` and `x`,
  since that would entail going counter-clockwise, which is not allowed
  (since, for illustration, we chose the ring to go clockwise)
- [btw_total] `∀ w x y, btw w x y ∨ btw w y x ∨ w = x ∨ w = y ∨ x = y`
-/
instantiate btwn : Between node

/- We open the `Between` and `TotalOrder` namespaces, so that we can use the
`le` and `btw` relations without prefixing them with `tot` and `btwn`. -/
open Between TotalOrder

/-
We model the state of this protocol as follows, with two relations:

- `leader : node → Bool` tracks which nodes believe they are the leader;
  `leader n = true` means node `n` believes it is the leader.

   The safety property is that at most one node can be elected as leader, i.e.
   `∀ n1 n2, leader n1 ∧ leader n2 → n1 = n2`. We will specify this later.

- `pending : node → node → Bool` tracks messages in transit, where
  `pending id dst` means there is a message containing node `id`'s ID that has
  been sent to node `dst`. Note that, for simplicity, we do not model the
  immediate sender of the message, but only its _original_ sender (which
  matches the ID within the message). There is no need to track the full path
  a message has taken through the ring.

  NOTE: we declare relations as `Bool`-valued (rather than `Prop`-valued).
  This keeps the state executable, which is what lets Veil's explicit-state
  model checker run the specification.
-/
relation leader : node → Bool

-- `pending id dst = true` means there is a message containing node `id`'s ID
-- that has been sent to (and can be received by) node `dst`.
-- (This shows the alternative syntax with named arguments.)
relation pending (id : node) (dst : node) : Bool

/- This assembles the previously declared components into the state type of the
`Ring` transition system. Conceptually, the generated `State` corresponds to
the following `structure` definition:

```lean
structure State where
  leader : node → Bool
  pending : node → node → Bool
```

(The actual generated type is parametric in the concrete runtime
representation of each field, which lets the model checker use efficient data
structures; you can inspect it with `#print State`.) -/
#gen_state

/- Veil's model of a specification is a state transition system. Having just
defined the type of states, we now define the initial state.

Every Veil model starts in a _default_ state (with every field set to its
default value), which is then immediately, atomically modified by the
(possibly non-deterministic) imperative program specified in the `after_init`
block. In practice, you can think of `after_init` as directly specifying the
initial state(s). -/
after_init {
  /- In assignments (and `safety` / `invariant` clause declarations), capital
  letters are implicitly universally quantified. This is a convention we adopt
  from Ivy. For instance, `leader N := false` means that for all nodes `n`,
  `leader n = false`. -/
  leader N := false
  /- i.e. `∀ m n, pending m n := false`,
    or equivalently: `pending := fun M N => false` -/
  pending M N := false
}

/-
_Actions_ in Veil are imperative code fragments that modify the state. For
verification purposes, Veil "compiles" actions to two-state transition
relations (i.e. predicates over a pre-state and a post-state); for execution
(testing), it uses their imperative semantics directly.

Here we define an action `send`, with parameters `n` and `next` of type `node`,
that specifies what node `n` does when it initiates the protocol, i.e. it sends
a message containing its own ID to its successor (`next`).
-/
action send (n next : node) {
  /- A `require` statement specifies a precondition that must be satisfied for
  the action to take effect / trigger. Here we encode that `next` is indeed
  the successor of `n` in the ring. -/
  require n ≠ next ∧ ∀ Z, ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

/- Instead of "inlining" the condition for a node `next` to be the successor of
`n` in all our actions, we can define a `ghost` `relation`, i.e. a derived
definition given in terms of the "real" state and theory. (In this case,
`isNext` does not in fact depend on the mutable state, but it could.) -/
ghost relation isNext (n next : node) :=
  (n ≠ next) ∧ (∀ N', (N' ≠ n ∧ N' ≠ next) → ¬ btw n N' next)

/- `n` receives a message containing `sender`'s ID, and potentially forwards
it to `next`. -/
action recv (sender n next : node) {
  require isNext n next
  require pending sender n
  /- We use non-deterministic assignment to model that the message may or may
  not be removed (i.e. it can potentially be received many times). -/
  pending sender n := *

  /- This is equivalent to the following Veil code:
  ```lean
  let isPresent ← pick Bool
  pending sender n := isPresent
  ```

  Non-deterministic assignment is more general and also lets us express things
  like `pending ID N := *` (the entirety of the `pending` relation becomes
  indeterminate). To obtain a non-deterministic value _constrained_ by a
  predicate, use the Hilbert-choice binding form `let x :| P`.
  -/

  /- Veil `action`s are in fact an extended form of `do` notation, so you can
  use standard Lean syntax and `do`-notation features like `let mut` in them. -/
  if (sender = n) then
    leader n := true
  else
    if (le n sender) then
      pending sender next := true
}

/- This is the safety property we want to establish. `L1` and `L2` are
implicitly universally quantified, i.e. this means:
`∀ (L1 L2 : node), leader L1 ∧ leader L2 → L1 = L2` -/
safety [single_leader] leader L1 ∧ leader L2 → L1 = L2

/- These invariant clauses together with the safety property above form an
inductive invariant. COMMENT THEM OUT to see how Veil can be used to manually
discover invariants, guided by counterexamples to induction. -/

invariant [leader_greatest] leader L → le N L
invariant [receive_self_msg_only_if_greatest] pending L L → le N L
invariant [no_bypass] pending S D ∧ btw S N D → le N S

/- Before we can operate on the specification in any way (e.g. check it), we
must run the `#gen_spec` command. -/

#gen_spec

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-transition-local/results/batch-events/Tutorial_Ring__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d1__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d1__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d1__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any action
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d1__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d1__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 2 actions
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d2__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d2__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 2 actions
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d2__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d2__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d2__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 4 actions
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d4__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d4__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d4__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 4 actions
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d4__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d4__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_6] {
  any 8 actions
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d8__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d8__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_7] {
  any 8 actions
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d8__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d8__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d8__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_8] {
  any 16 actions
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d16__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d16__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d16__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_9] {
  any 16 actions
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d16__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d16__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_10] {
  any 32 actions
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d32__local__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d32__local__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data
    __veil_bmc_if_local (

    symbolic_bench_phase "split_trace" __veil_bmc_split_trace
    symbolic_bench_phase "nextSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [nextSimp])
    symbolic_bench_phase "hoist" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "prepare_hints" __veil_bmc_check_hints
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (__veil_bmc_hyps simp +instances (failIfUnchanged := false) only [smtSimp])
    symbolic_bench_phase "dsimp2" (__veil_bmc_hyps dsimp +instances (failIfUnchanged := false) [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "check_hints" __veil_bmc_check_hints
    ) else (

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    )
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_11] {
  any 32 actions
  assert (∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2)
} by
  symbolic_bench_extract "/tmp/veil-transition-local/results/events/Tutorial_Ring__d32__early__default.jsonl" "/tmp/veil-transition-local/results/queries/Tutorial_Ring__d32__early__default.smt2" (
    symbolic_bench_phase "early_intros" symbolic_bench_intro_data

    symbolic_bench_phase "nextSimp" (veil_simp +instances only [nextSimp])
    symbolic_bench_phase "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
    symbolic_bench_phase "intros" veil_intros
    symbolic_bench_phase "destruct" veil_destruct
    symbolic_bench_phase "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
    symbolic_bench_phase "smtSimp" (veil_simp +instances only [smtSimp])
    symbolic_bench_phase "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  )
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-transition-local/results/events/Tutorial_Ring__d32__early__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end Ring
