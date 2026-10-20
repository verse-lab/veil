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
set_option veil.experimental.bmcCache false

/-! # FloodSet: A Synchronous Crash Fault Agreement Protocol

This file walks through the process of modelling, specifying, testing, and
verifying a classic distributed protocol in Veil, using the full spectrum of
verification modalities the framework offers: explicit-state model checking,
symbolic bounded model checking, SMT-based invariant checking, and interactive
proof. It follows the presentation in Chapter "Multi-Modal Verification of
Distributed Protocols" of [George Pîrlea's PhD
dissertation](https://pirlea.net/papers/thesis-draft.pdf).

We model the _FloodSet_ protocol, described by Nancy Lynch in Chapter 6 of her
textbook on distributed algorithms (Lynch, 1996), and follow her presentation.

## Synchronous Fail-Stop Setting

There are `n` processes, arranged in a fully connected network. Execution
proceeds in _synchronous rounds_: in each round, every process first sends
messages to other processes, then receives all messages sent to it in that
round, and finally performs a local state transition. All messages sent in a
round are delivered in the same round—links are perfectly reliable and
messages are not dropped.

Up to `f` of the `n` processes may fail by _crashing_: a crashed process stops
executing permanently (a _fail-stop_ failure). Crucially, a crash may occur in
the middle of a round's message-sending step, so that only an arbitrary subset
of the messages a process intended to send are actually delivered.

## Agreement Problem

Each process starts with an input from a set of values `V` and must eventually
output a decision value, also from `V`. The correctness conditions are:

- **Agreement**: no two processes decide differently.
- **Validity**: if all inputs are `v`, then `v` is the only decision.
- **Termination**: every non-faulty process eventually decides.

## FloodSet Algorithm

Each process maintains a set `W ⊆ V` of values it has seen, initially
containing only its own input. For `f+1` rounds, every process broadcasts its
`W` to all other processes and adds all received values to its own `W`. At the
end of the `f+1` rounds, the process decides based on its `W` set.

Lynch's presentation decides the fixed default value `v₀` if `W` is not a
singleton. In fact, _any_ deterministic decision rule suffices to guarantee
correctness. We assume the set of values `V` is totally ordered and have
processes choose the _minimum_ value in their final `W` set. This decision
rule makes the protocol satisfy a stronger validity property:

- **Strong Validity**: every decision value is some process' input.

## Correctness

The correctness proof is structured around three lemmas. Let `W_i(r)` denote
the value of `W` at process `i` at the end of round `r`, and say a process is
_active_ after `r` rounds if it has not crashed by the end of round `r`.

- **Saturation**: if no process crashes during a particular round `r`, then
  `W_i(r) = W_j(r)` for all `i` and `j` active after `r` rounds.
- **Stability**: if `W_i(r) = W_j(r)` for all `i`, `j` active after `r`
  rounds, this remains true for every round `r' ≥ r`.
- **Uniformity**: if processes `i` and `j` are both active after `f+1` rounds,
  then `W_i(f+1) = W_j(f+1)`.

The critical insight is a _pigeonhole argument_: since at most `f` processes
crash across `f+1` rounds, at least one round must be crash-free. Saturation
then gives the precondition for Stability, from which Uniformity follows.
Finally, since all active nodes agree on `W` and they all use the same
deterministic rule to decide, no two processes decide differently.

We will see this argument reflected in the inductive invariant below.
-/

veil module FloodSet

/-! ## Parameters and Theory

The protocol is parametrised by the set of nodes, the (totally ordered) set of
values, and by the maximum number of crash failures `f`. The `type` command
declares an uninterpreted sort (a parameter of the module); `instantiate`
introduces typeclass assumptions about it; and `immutable` fields form the
system's _theory_—state that cannot change during execution. -/

type node
type value
instantiate val_ord : TotalOrder value

immutable individual f : Nat                        -- maximum number of crash failures

/-! ## State Space

It is here that we face our first real design decisions: Should we represent
the set of seen values as a `List`? Do we need a field to track whether a
particular node has crashed (and if yes, in which round)? Should this have
type `node → Option Nat`?

The intuition for these decisions comes with experience, but a good rule of
thumb is to stay within first-order logic as much as possible (avoid `List`
and `Option`) and to represent as little structure as one can get away with
(prefer `relation` over `function`).

Nodes start with an input value, and eventually output a decision. We model
decisions as sets (i.e. relations), to be able to state that only one decision
is taken per process. Each node maintains a set `W` of values it has seen. We
also keep track of crashes.

Note that Veil's abstractions are designed for asynchrony, so we must _encode_
the synchronous fail-stop setting: a global `round` counter, and per-node
crash bookkeeping (`crashed`, `crashedInRound`, `numCrashed`). -/

individual round : Nat                              -- current round number (0 to f+1)
function initialValue : node → value                -- initial proposal for each node
relation W (n : node) (v : value) : Bool            -- W set per node
relation decision (n : node) (v : value) : Bool     -- decision value per node, initially ∅
function crashed (n : node) : Bool                  -- has this node crashed?
function crashedInRound (n : node) : Nat            -- which round did it crash in?
individual numCrashed : Nat                         -- total number of crashes so far

/-! ## Ghost Definitions

It is often helpful to write _derived_ definitions, which depend on the theory
and state of the system. Despite the name, these are not ghost _state_, but
definitions (note the `:=`) derived from the system's state. -/

ghost relation alive (n : node) := ¬crashed n
ghost relation crashedInAPreviousRound (n : node) := (crashed n ∧ crashedInRound n < round)

/-! ## Initial Configuration

The initial configuration is easy to specify. Initial values are arbitrarily
chosen (`:= *` is unconstrained non-deterministic assignment). Every node has
seen only its own proposal. No node has decided. The global round counter is
0. No node has crashed.

Capitalised variables (`N`, `V`) are implicitly universally quantified—a
syntactic convention Veil adopts from Ivy. The quantified variables are bound
on the right-hand side of assignments, so `W N V := (V == initialValue N)`
means "for all `n` and `v`, `W n v` holds iff `v` is `n`'s initial value." -/

after_init {
  initialValue := *
  round := 0
  W N V := (V == initialValue N)
  decision N V := false
  crashed N := false
  crashedInRound N := 0
  numCrashed := 0
}

/-! ## Crash Failures

We model crashes as happening _within_ rounds. A node can crash only if it is
alive and fewer than `f` crashes have occurred. The transition marks the node
as crashed, records the round, and increments the crash counter.

`require` expresses the precondition of the transition: when the action is
invoked by the environment, a failing `require` means the transition is simply
not enabled (the execution is discarded, with no blame); when a procedure is
called from another procedure, `require` instead behaves as an assertion the
caller must satisfy. -/

action crash (n : node) {
  require numCrashed < f
  require alive n
  crashed n := true
  crashedInRound n := round
  numCrashed := numCrashed + 1
}

/-! ## Synchronous Round Step

We model the delivery pattern of an entire round as a non-deterministically
chosen relation: a node that crashed in a _previous_ round delivers to nobody,
and a node that is alive delivers to everybody. A node that crashed _in the
current round_ falls into neither case, so delivery is unconstrained for
it—it may deliver to any subset of receivers, capturing the fail-stop
behaviour of a node that crashes partway through sending.

The binding form `let x :| P` is Veil's constrained non-deterministic choice
(Hilbert choice): it gives a value `x` satisfying the predicate `P`. Here we
make a _higher-order_ choice—`delivery` is a value of type
`node → node → Bool`. Non-determinism is _demonic_ for verification (all
choices must be safe) and _angelic_ for execution (some satisfying choice is
produced).

Finally, a node knows a value at the end of the round iff it either already
knew it, or received it from some sender that knew it. -/

action advanceRound {
  require round < f + 1
  -- We model message delivery by picking a delivery relation that determines
  -- which messages from each sender are received by which receivers.
  let delivery : (node → node → Bool) :|
    (∀ (sender : node),
      (crashedInAPreviousRound sender → (∀ (receiver : node), ¬ delivery sender receiver)) ∧
      (alive sender → (∀ (receiver : node), delivery sender receiver)))
  -- A node knows a value at the end of this round iff it either already knew it,
  -- or received it from some sender that knew it.
  W N V := decide $ W N V ∨ (alive N ∧ ∃ sender, delivery sender N ∧ W sender V)
  round := round + 1
}

/-! ## Deterministic Decision

In round `f+1`, each live node chooses the minimum element of its knowledge
set, as determined by the total order on values. We place the decision rule
into a separate `procedure` to keep the model clear; the action _calls_ the
rule to pick the value, which the node records as its decision.

(`procedure`s are internal helper routines that cannot be invoked by the
environment directly; `pick` produces an unconstrained non-deterministic
value, which the subsequent `assume` constrains.) -/

procedure deterministicDecision (n : node) {
  let v ← pick value
  assume W n v ∧ (∀ v', W n v' → val_ord.le v v')
  return v
}

action nodeDecide (n : node) {
  require round = f + 1
  require alive n
  require ¬(∃ v, decision n v)
  let v ← deterministicDecision n
  decision n v := true
}

/-! ## Specification: Safety Properties

The model above describes _how_ the protocol operates. To test or verify it,
we need a _specification_ of what it is supposed to do. We declare the two
safety properties via the `safety` command (Termination is a liveness
property, which Veil does not yet handle). -/

safety [agreement]
  ∀ n₁ n₂ v₁ v₂, decision n₁ v₁ ∧ decision n₂ v₂ → v₁ = v₂

safety [strong_validity]
  ∀ n v, decision n v → ((∃ m, initialValue m = v))

/-! ## Verification: Interactive Invariant Discovery

The `#check_invariants` command (at the bottom of this file) tries to prove
that the conjunction of all `safety` and `invariant` clauses is an _inductive
invariant_: one that holds in all initial states and is preserved by every
transition. With only the two safety properties above, it is not—Veil shows
_counterexamples to induction_ (CTIs): a pre-state satisfying the candidate
invariant, a transition, and a post-state violating some clause.

CTIs do not show the system is wrong. They show that the candidate invariant
also admits _unreachable_ states from which the system can transition into bad
states. To verify the system, we _strengthen_ the invariant with clauses that
rule out these unreachable pre-states—repeating until no CTIs remain. The
danger is adding a clause that is not actually invariant (i.e. one that
excludes a reachable state); the model checker call below catches such
mistakes early, before we chase unprovable goals.

The clauses below were discovered interactively through exactly this process.
The first CTI (a state where a node had decided a non-minimal value, seen
values that were nobody's input, crashed despite `f = 0`, etc.) yields the
first batch: -/

invariant [every_seen_is_someones_initial]
  ∀ n v, W n v → (∃ m, initialValue m = v)

invariant [decision_minimum_seen]
  ∀ n v, decision n v → (∀ v', W n v' → val_ord.le v v')

invariant [crash_limit]
  numCrashed ≤ f

-- We would ideally say `numCrashed` is the cardinality of the `crashed` set;
-- Veil's standard library has finite sets with cardinalities, but rather than
-- change the encoding we eliminate the specific inconsistency observed in the
-- CTI and see whether similar counterexamples arise later.
invariant [no_crashes_def]
  numCrashed = 0 ↔ ∀ n, ¬ crashed n

-- A node that decided and crashed must have crashed after the protocol ended.
invariant [decision_crashed_after_end]
  ∀ n v, (decision n v ∧ crashed n) → crashedInRound n ≥ f + 1

-- A semantic weakening of the above, "factoring out" the crash:
invariant [decision_only_at_end]
  ∀ n v, decision n v → round ≥ f + 1

invariant [crashed_in_round_le_round]
  ∀ n, crashedInRound n ≤ round

invariant [initial_value_in_W]
  ∀ n, W n (initialValue n)

invariant [decided_in_seen]
  ∀ n v, decision n v → W n v

invariant [crashedInRound_default]
  ∀ n, alive n → crashedInRound n = 0

/-! ## The Crux: Saturation

The remaining CTIs get at the heart of the correctness argument: states that
imply a crash-free round has happened, yet whose `W` sets are not
synchronised. We need to express Saturation and Stability as invariant
clauses.

First, we express that a crash-free round occurred, quantifying existentially
over round numbers.

The `participants_have_equal_W_after_crash_free` clause is a combination of
Saturation and Stability: if there was a crash-free round in the past, then
all nodes participating in the current round (alive, or crashed in this very
round) have equal `W` sets.

The two `crash_round_gap` clauses encode the pigeonhole principle connecting
the crash counter to the existence of a crash-free round: if the execution has
had more rounds than crashes, some past round was crash-free; and if it has
had exactly as many, then either some past round was crash-free or the current
one is. -/

ghost relation crashedNow (n : node) := crashed n ∧ crashedInRound n = round
ghost relation roundParticipant (n : node) := alive n ∨ crashedNow n
ghost relation crashFreeRound (r : Nat) :=
  ∀ n, ¬ crashed n ∨ crashedInRound n ≠ r
ghost relation hadCrashFreeRound := ∃ r, r < round ∧ crashFreeRound r

invariant [crash_round_gap]
  numCrashed < round → hadCrashFreeRound

invariant [crash_round_gap_or_current]
  numCrashed = round → hadCrashFreeRound ∨ crashFreeRound round

invariant [participants_have_equal_W_after_crash_free]
  hadCrashFreeRound → ∀ n₁ n₂ v, roundParticipant n₁ ∧ roundParticipant n₂ → (W n₁ v = W n₂ v)

/- Before we can operate on the specification (check it, model check it, etc.)
we must assemble it with `#gen_spec`. -/

#gen_spec
run_cmd discard <| _root_.Veil.Verifier.waitFilteredSync _root_.Veil.Verifier.isDoesNotThrow

run_cmd Lean.Elab.Command.liftTermElabM do
  IO.FS.writeFile "/tmp/veil-action-cache/results/batch-events/Tutorial_FloodSet__local__default__batch1.ready" (toString (← IO.monoMsNow))

set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option veil.smt.trust true
set_option veil.smt.finiteModelFind true

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_0] {
  any action
  assert (¬ (∀ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 → v1 = v2))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d1__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d1__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d1__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_1] {
  any 2 actions
  assert (¬ (∀ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 → v1 = v2))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d2__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d2__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d2__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_2] {
  any 4 actions
  assert (¬ (∀ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 → v1 = v2))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d4__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d4__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d4__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_3] {
  any 8 actions
  assert (¬ (∀ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 → v1 = v2))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d8__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d8__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d8__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_4] {
  any 16 actions
  assert (¬ (∀ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 → v1 = v2))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d16__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d16__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d16__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "begin"

unsat trace [symbolic_bmc_probe_5] {
  any 32 actions
  assert (¬ (∀ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 → v1 = v2))
} by
  symbolic_bench_extract "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d32__local__default.jsonl" "/tmp/veil-action-cache/results/queries/Tutorial_FloodSet__d32__local__default.smt2" (
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
  Lean.withOptions (fun opts => opts.set `symbolicBench.eventPath "/tmp/veil-action-cache/results/events/Tutorial_FloodSet__d32__local__default.jsonl") do
    symbolicBenchEvent "query_elaboration" "query_elaboration" "end"

end FloodSet
