import Veil

/-!
# FloodSet Consensus Protocol

FloodSet is a synchronous consensus protocol that tolerates up to `t` crash
failures over `t+1` rounds. The protocol is remarkably simple:

1. Each node starts with an initial value (its proposal)
2. In each round, all alive nodes broadcast their seen values to everyone
3. After `t+1` rounds, each node decides on the minimum value it has seen

The key insight is the **pigeonhole principle**: with at most `t` crashes spread
over `t+1` rounds, at least one round must be crash-free. In that round, all
alive nodes successfully exchange their seen sets and become synchronized. Once
synchronized, all alive nodes have identical seen sets and will decide on the
same minimum value, guaranteeing agreement.

Partial delivery: When a node crashes mid-round, it may have sent its values to
some nodes but not others. We model this with `receivedFromDead`.
-/

veil module FloodSet

--------------------------------------------------------------------------------
-- PART 1: STATE
--
-- Veil state declarations:
-- - `type` declares an uninterpreted sort (abstract type)
-- - `instantiate` provides a typeclass instance for a type
-- - `immutable individual` declares a constant (theory parameter)
-- - `individual` declares a mutable scalar state component
-- - `relation` declares a mutable predicate (function to Bool)
-- - `#gen_state` finalizes the state type from all declarations
--------------------------------------------------------------------------------

-- Abstract types for nodes and values
type node
type value

-- [NEW] A type of sets of nodes
type nodeSet
instantiate nset : TSet node nodeSet

-- Values must be totally ordered (for picking the minimum)
instantiate val_ord : TotalOrder value
open TotalOrder


immutable individual t : Nat

-- [NEW] All nodes in the system
immutable individual allnodes : nodeSet

individual round : Nat
individual crashCount : Nat-- Protocol state components:
-- - t: maximum crash failures tolerated (immutable theory parameter)
-- - round: current round number (0 to t+1)
-- - crashCount: total number of crashes so far
-- - seen: values each node has observed
-- - alive: whether each node is still functioning
-- - decision: the decided value (if any) for each node
-- - crashedInThisRound: nodes that crashed in the current round (before advanceRound)
-- - initialValue: snapshot of each node's initial proposal (for extended validity)


function initialValue : node → value
relation seen : node → value → Bool
relation decision : node → value → Bool

-- [NEW] set of alive nodes
individual dead : nodeSet
individual crashedInThisRound : nodeSet

-- [NEW] Representing heard-from node-wise
function receivedFrom: node → nodeSet

#gen_state

--------------------------------------------------------------------------------
-- PART 2: ACTIONS
--------------------------------------------------------------------------------

ghost relation alive (n : node) := ¬ (nset.contains n dead)

-- Initial state: each node has exactly one proposal value
after_init {
  initialValue := *
  seen N V := initialValue N == V

  dead := nset.empty
  decision N V := false
  round := 0
  crashCount := 0

  -- [NEW] No one has received from anyone initially
  receivedFrom N := nset.insert N (nset.empty)
  crashedInThisRound := nset.empty
}

-- Crash one alive node (can happen multiple times per round, up to t total)
action crash (n : node) {
  require round < t + 1
  require crashCount < t
  require alive n

  dead := nset.insert n dead
  crashedInThisRound := nset.insert n crashedInThisRound
  crashCount := crashCount + 1

}

-- Advance to next round: alive nodes exchange values, with possible partial
-- delivery from nodes that crashed this round (modeled by receivedFromDead)
action advanceRound {
  require round < t + 1

  -- [NEW] Which nodes hear from which dead in this round
  let hearsFromDead <- pick (node → nodeSet)
  assume ∀ n m, nset.contains m (hearsFromDead n) →
                nset.contains m crashedInThisRound

  -- Nodes exchange values
  seen N V := seen N V ||
    alive N &&
    -- Get from nodes that are either alive or in hearsFromDead N
    decide (∃ m, alive m ∧ seen m V
               ∨ nset.contains m (hearsFromDead N) ∧ seen m V)

  -- [NEW] Updating who received from
  let aliveSoFar := nset.diff allnodes dead

  -- Received from alive ones
  receivedFrom N := nset.union (receivedFrom N) aliveSoFar
  -- Received from some dead ones too
  receivedFrom N := nset.union (receivedFrom N) (hearsFromDead N)

  -- Reset crash-related bookkeeping for the next round
  crashedInThisRound := nset.empty
  round := round + 1
}

-- Final decision: after t+1 rounds, pick the minimum seen value
action nodeDecide (n : node) {
  require round = t + 1
  require alive n

  let v :| seen n v
  assume ∀ w, seen n w → le v w
  decision n V := V == v
}

-- [NEW] a process may decide in round i,
-- if it received the values from all but i processes
-- [Warning] This action violates safety!

-- action fastDecide(n : node) {
--   require alive n

--   -- The following seems wrong - Lace finds a violation
--   require nset.count (receivedFrom n) ≥ nset.count allnodes - round

--   -- Is this a correct one?
--   -- require nset.count (receivedFrom n) = nset.count allnodes

--   let v :| seen n v
--   assume ∀ w, seen n w → le v w
--   decision n V := V == v
-- }


--------------------------------------------------------------------------------
-- PART 3: SAFETY AND INVARIANTS
--------------------------------------------------------------------------------

-- Main safety properties
safety [agreement]
  ∀ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 → v1 = v2

-- Validity: decided value was some node's initial proposal
safety [validity]
  ∀ n v, decision n v → (∃ m, initialValue m == v)

-- All nodes contains all nodes
safety [all_nodes]
  ∀ n, nset.contains n allnodes

-------------------------------------------------------------
-- Reachability checks (commented out after validation):
-- These temporarily defined "bad" safety properties prove interesting states
-- are reachable by expecting the model checker to find violations.
-------------------------------------------------------------

-- 1. Decision is reachable (protocol can terminate)
-- Expected: violation found (meaning decisions ARE reachable)
--
-- safety [no_decision] ∀ n v, ¬decision n v

-- 2. Crashes are possible (not all nodes survive)
-- Expected: violation found (meaning crashes ARE possible)
--
-- safety [no_crashes] ∀ n, alive n

-- 3. Dead nodes may have different seen sets than alive nodes
-- Expected: violation found (dead nodes can diverge from alive ones)
--
-- safety [dead_same_as_alive] ∀ n1 n2 v, round > 0 → ¬alive n1 ∧ alive n2 → (seen n1 v = seen n2 v)

-- 4. Nodes can see multiple values (non-trivial seen sets) in non-init rounds
-- Expected: violation found (nodes can accumulate multiple values)
--
-- safety [single_value_only] ∀ n v1 v2, round > 0 → seen n v1 ∧ seen n v2 → v1 = v2

-- 5. [NEW] A node can make a decision in non-last round
-- Expected: violation finds examples of fast decisions
--
-- safety [fast_decition] ∀ n v, decision n v → round = t + 1

#gen_spec

--------------------------------------------------------------------------------
-- PART 4: MODEL CHECKING
--
-- `#model_check` exhaustively explores all reachable states for concrete type
-- instantiations. The first argument instantiates abstract types (e.g., node,
-- value) with finite types (e.g., Fin 3). The second argument provides values
-- for immutable theory parameters (e.g., t := 1).
--
-- The checker verifies that all safety properties and invariants hold in every
-- reachable state. If a violation is found, it reports the violating state.
--
-- IDE tip: Place cursor on `#model_check` to see exploration progress and
-- the number of states explored. If a violation is found, a trace is shown.
--------------------------------------------------------------------------------

-- Small instance, one crash

abbrev nodeSize := 3 -- Anything larger will cause OOM error (sorry, working on it!)
abbrev valueSize := 2
abbrev numFailures := 1

-- The check finds a bug in this version, hence it's commented out

#model_check { node := Fin nodeSize,
               nodeSet := (Std.ExtTreeSet (Fin nodeSize) compare),
               value := Fin valueSize }
             { t := numFailures,
               allnodes := (Std.ExtTreeSet.empty.insertMany (List.finRange nodeSize)) }

end FloodSet
