module

public import Veil

/-!
Safety translation of MongoDB's OrderedTicketSemaphore.
Source: https://github.com/mongodb/mongo/blob/43180330a36009ecd18a08325fd4fa2a043810a9/src/mongo/tla_plus/Concurrency/OrderedTicketSemaphore/OrderedTicketSemaphore.tla
Copyright 2026 MongoDB, Inc. Source licensed under CC BY 3.0 US:
https://creativecommons.org/licenses/by/3.0/us/
See Benchmarks/TLA/OrderedTicketSemaphore/LICENSE for attribution and license links.

The six actions and four safety invariants follow the TLA+ source. Lean's types
encode `TypeOK`. `Fairness`, `WaitingLeadsToHolding`, and `NeverWaitsIndefinitely` are
outside this safety model. In particular, permits may be negative:
nonnegative permits is deliberately not asserted as an invariant.

The client type represents `AllClients`, including the distinguished resizer. The
set constant `AllClients` gives `TakenMatchesHolding`'s finite sum over that domain.
The model-checking instance is the TLC sizing run with five ordinary clients
(the upstream MC configuration has four). The local TLA+ harness uses the same
capacity bound, `permits + taken <= 9`, and TLC's default deadlock check.
-/

veil module OrderedTicketSemaphore

type client
type ClientSet

@[veil_decl]
structure Waiter (client : Type) where
  thread : client
  awake : Bool
  interruptible : Bool

instantiate clientSet : TSet client ClientSet

immutable individual AllClients : ClientSet
immutable individual ResizerClient : client
immutable individual InitPermits : Int
immutable individual ResizerClientMaxTickets : Int
immutable individual ResizeDelta : Nat

individual permits : Int
individual taken : Int
individual waitQueue : List (Waiter client)
function heldTickets : client → Int

set_option veil.deferVCGeneration true

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

assumption [initial_capacity] InitPermits ≥ ResizerClientMaxTickets
assumption [all_clients_complete] ∀ c : client, c ∈ AllClients

-- findIdx returns q.length if every entry is awake. The index comparison then
-- changes nothing. Int.toNat similarly makes nonpositive n a no-op.
-- Wake a contiguous segment from the first sleeping entry, as in the source.
def WakeFirstN {client : Type} (q : List (Waiter client)) (n : Int) :
    List (Waiter client) :=
  let first := q.findIdx (fun w => !w.awake)
  q.mapIdx fun i w =>
    if first ≤ i ∧ i < first + n.toNat then { w with awake := true } else w

-- WaiterIndex(waitQueue, t) > 0: some queue entry belongs to t.
ghost relation IsWaiting (t : client) :=
  ∃ w ∈ waitQueue, w.thread = t

ghost relation IsHolding (t : client) := heldTickets t > 0

ghost relation CanAcquire (t : client) :=
  ¬ IsWaiting t ∧
    if t = ResizerClient then heldTickets t < ResizerClientMaxTickets
    else heldTickets t = 0

ghost relation CanSkipQueue := permits > (waitQueue.length : Int)

after_init {
  permits := InitPermits
  taken := 0
  waitQueue := []
  heldTickets T := 0
}

action TryAcquire (t : client) {
  require CanAcquire t
  require CanSkipQueue
  permits := permits - 1
  taken := taken + 1
  heldTickets t := heldTickets t + 1
}

action Acquire (t : client) (interruptible : Bool) {
  require CanAcquire t
  require ¬ CanSkipQueue
  waitQueue := waitQueue ++ [{ thread := t, awake := false, interruptible }]
}

action WakeAndConsume (t : client) {
  require IsWaiting t
  let idx := waitQueue.findIdx (fun w => w.thread == t)
  require (waitQueue.getD idx default).awake
  waitQueue := waitQueue.eraseIdx idx
  -- No positive-permits guard: a resize may have made permits negative.
  permits := permits - 1
  taken := taken + 1
  heldTickets t := heldTickets t + 1
}

action DoRelease (t : client) {
  require IsHolding t
  require ¬ IsWaiting t
  permits := permits + 1
  taken := taken - 1
  heldTickets t := heldTickets t - 1
  -- This condition reads the updated permits, corresponding to permits' > 0.
  if permits > 0 then {
    waitQueue := WakeFirstN waitQueue 1
  }
}

action ImmediateResize {
  -- Enumerate the inclusive interval -ResizeDelta .. ResizeDelta.
  let offset : Nat :| offset ∈ List.range (2 * ResizeDelta + 1)
  let n := (offset : Int) - (ResizeDelta : Int)
  require ¬ IsHolding ResizerClient
  require ¬ IsWaiting ResizerClient
  require permits + taken + n ≥ ResizerClientMaxTickets
  permits := permits + n
  waitQueue := WakeFirstN waitQueue permits
}

action Interrupt (t : client) {
  require IsWaiting t
  let idx := waitQueue.findIdx (fun w => w.thread == t)
  let waiter := waitQueue.getD idx default
  require waiter.interruptible
  waitQueue := waitQueue.eraseIdx idx
  -- Preserve the old entry's awake flag before removing it.
  if waiter.awake then {
    waitQueue := WakeFirstN waitQueue 1
  }
}

invariant [TakenNonNegative] taken ≥ 0

invariant [TakenMatchesHolding]
  taken = (clientSet.toList AllClients).foldl (fun total t => total + heldTickets t) 0

invariant [UniqueWaiters] (waitQueue.map (·.thread)).Nodup

invariant [AwakeBeforeNonAwake]
  waitQueue.Pairwise (fun earlier later => earlier.awake = false → later.awake = false)

-- A model-checking bound, not an extra action guard or a safety property.
state_constraint [TicketLimit] permits + taken < 10

-- Match TLC's enabled deadlock check. Only ImmediateResize changes permits + taken,
-- and whenever it is enabled some delta stays within TicketLimit, so no state loses
-- all of its successors to the constraint.
termination false

#gen_spec
#gen_executable

-- The check below uses the instance of the TLC model
-- `Benchmarks/TLA/OrderedTicketSemaphore/OrderedTicketSemaphore.cfg`, which TLC runs on
-- `MCOrderedTicketSemaphore.tla`. It is commented out; uncomment it to run it.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `client := Fin 6`: the clients are `0..5`, the resizer included
--   (cfg: `Clients = {c1, c2, c3, c4, c5}`, to which the spec adds `ResizerClient`).
-- * `ClientSet := OrdList _`: `OrdList` has the `TSet` instance that the `instantiate` line above
--   requires.
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `AllClients := OrdList.ofList (List.finRange 6)`: the set of all six clients, the spec's
--   `AllClients == Clients \union {ResizerClient}`. The `assumption [all_clients_complete]` above
--   checks that it contains every client.
-- * `ResizerClient := 5`: client `5` is the resizer. The cfg has no counterpart, since the spec
--   defines `ResizerClient == "ResizerClient"`.
-- * `InitPermits := 3`: the initial number of permits (cfg: `InitPermits = 3`).
-- * `ResizerClientMaxTickets := 2`: the most tickets the resizer holds at once
--   (cfg: `ResizerClientMaxTickets = 2`).
-- * `ResizeDelta := 3`: the most tickets of an immediate resize (cfg: `ResizeDelta = 3`).
--
-- Before searching, `#model_check` also checks the `assumption [initial_capacity]` above, which
-- is the spec's `ASSUME InitPermits >= ResizerClientMaxTickets`.
--
-- The other settings of the cfg:
-- * `CONSTRAINT BenchmarkBound`: the `state_constraint [TicketLimit]` above, as
--   `BenchmarkBound == permits + taken <= 9`. Unlike TLC, Veil does not check the invariants in
--   the states that the constraint drops.
-- * `INVARIANTS TypeOK TakenNonNegative ... AwakeBeforeNonAwake`: `#model_check` checks every
--   `invariant` of the module, which here has the same names except `TypeOK`. Lean's types
--   ensure `TypeOK`.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock.
-- Options:
-- * `compiled` runs the search only in a compiled checker, not in Lean's interpreter.
-- * `(seenSet := HAMTMapShard)`: the sharded map of visited states uses `HAMTMapShard`.
/- EVAL
#model_check compiled
  { client := Fin 6, ClientSet := OrdList _ }
  { AllClients := OrdList.ofList (List.finRange 6),
    ResizerClient := 5,
    InitPermits := 3,
    ResizerClientMaxTickets := 2,
    ResizeDelta := 3 }
  (seenSet := HAMTMapShard)
-/

end OrderedTicketSemaphore
