import Veil

/-!
# Paxos – FOL/Relational Encoding (Validation Vehicle)

This file is a hybrid specification: Ivy-style relational state encoding with
TLA+-style ghost relations and invariants. It was derived from
`Examples/Ivy/PaxosFOL.lean` (the original Ivy encoding) by Claude Code, and
served as the key validation step in an AI-assisted verification effort.

Compared to the original Ivy encoding, this file:
1. Renames types (`round` → `ballot`) and relations (`proposal` → `two_a`, etc.)
2. Adds explicit acceptor state functions (`maxBal`, `maxVBal`, `maxVal`)
3. Uses TLA+-style action names (`Phase1a`, `Phase1b`, `Phase2a`, `Phase2b`)
4. Replaces EPR-style invariants with TLA+-style ones (`MsgInv1b/2a/2b`,
   `AccInv`, `VotedInv`, `VotedOnce`) and ghost relations (`VotedForIn`,
   `WontVoteIn`, `SafeAt`, `Chosen`)
5. Removes the explicit `decide` action — safety is expressed via the ghost
   `Chosen` predicate

Using this simpler encoding, we:
- Validated the spec via `#model_check` (not vacuous, no invariant violations)
- Discovered via `#check_invariants` that the invariant was **not inductive**
  (`Phase2b` did not preserve `Consistency`), and found the missing clause:
  `invariant [two_a_valid_ballot] ∀ b v, two_a b v → b ≠ tot.none`
- Ported the complete inductive invariant back to the TLA-style spec
  (`Paxos.lean`), identified discrepancies (missing assumptions, computational
  vs. logical encoding issues), and ultimately proved all VCs interactively
  in `Examples/Paxos/PaxosProof/`

See `README.md` in this directory for the full development story.
-/

veil module PaxosTLAStyle

type node      -- acceptors (called "acceptor" in TLA+)
type value
type quorum
type ballot    -- rounds/ballots

instantiate tot : TotalOrderWithZeroAndNone ballot
immutable relation member (N : node) (Q : quorum)

/-!
## Message Relations (Ivy-style relational encoding of TLA+ message set)

These correspond to the TLA+ message types:
- `one_a b` ≈ `{type: "1a", bal: b} ∈ msgs`
- `one_b n b maxVBal v` ≈ `{type: "1b", bal: b, maxVBal: maxVBal, maxVal: v, acc: n} ∈ msgs`
- `two_a b v` ≈ `{type: "2a", bal: b, val: v} ∈ msgs`
- `two_b n b v` ≈ `{type: "2b", bal: b, val: v, acc: n} ∈ msgs`
-/

relation one_a (R : ballot)
relation one_b (N : node) (R : ballot) (MAXVBAL : ballot) (V : value)
relation two_a (R : ballot) (V : value)
relation two_b (N : node) (R : ballot) (V : value)

/-!
## Acceptor Local State (TLA+-style)

- `maxBal[a]`: highest ballot acceptor a has participated in (responded to 1a)
- `maxVBal[a]`: highest ballot in which a has voted
- `maxVal[a]`: value a voted for in ballot maxVBal[a]
-/

function maxBal (N : node) : ballot
function maxVBal (N : node) : ballot
function maxVal (N : node) : value

#gen_state

/-!
## Assumptions
-/

assumption [quorum_intersection]
  ∀ (Q1 Q2 : quorum), ∃ (N : node), member N Q1 ∧ member N Q2

/-!
## Helper Relations for Comparisons
-/

-- Strict less than: x < y
ghost relation lt (x y : ballot) := tot.le x y ∧ x ≠ y
-- Greater than or equal: x >= y
ghost relation ge (x y : ballot) := tot.le y x
-- Strict greater than: x > y
ghost relation gt (x y : ballot) := tot.le y x ∧ x ≠ y

/-!
## Initial State

TLA+:
```
Init == /\ msgs = {}
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxBal  = [a \in Acceptors |-> -1]
        /\ maxVal  = [a \in Acceptors |-> None]
```
-/

after_init {
  one_a R := false
  one_b N R MAXVBAL V := false
  two_a R V := false
  two_b N R V := false
  maxBal N := tot.none
  maxVBal N := tot.none
  maxVal N := (default : value)
}

/-!
## Actions

These match the TLA+ action structure as closely as possible.
-/

/-!
### Phase 1a: Leader sends prepare request

TLA+:
```
Phase1a(b) == /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
              /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxVBal, maxBal, maxVal>>
```
-/

action Phase1a (b : ballot) {
  require b ≠ tot.none
  -- ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
  require ¬ one_a b
  -- Send([type |-> "1a", bal |-> b])
  one_a b := true
}

/-!
### Phase 1b: Acceptor responds to prepare with promise

TLA+:
```
Phase1b(a) ==
  \E m \in msgs :
     /\ m.type = "1a"
     /\ m.bal > maxBal[a]
     /\ Send([type |-> "1b", bal |-> m.bal, maxVBal |-> maxVBal[a],
               maxVal |-> maxVal[a], acc |-> a])
     /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
     /\ UNCHANGED <<maxVBal, maxVal>>
```
-/

action Phase1b (a : node) {
  -- \E m \in msgs : m.type = "1a" /\ m.bal > maxBal[a]
  let b : ballot ← pick
  require one_a b
  require gt b (maxBal a)
  -- Send([type |-> "1b", bal |-> b, maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a])
  one_b a b (maxVBal a) (maxVal a) := true
  -- maxBal' = [maxBal EXCEPT ![a] = b]
  maxBal a := b
}

/-!
### Phase 2a: Leader sends accept request (proposal)

TLA+:
```
Phase2a(b) ==
  /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
  /\ \E v \in Values :
       /\ \E Q \in Quorums :
            \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
               /\ \A a \in Q : \E m \in S : m.acc = a
               /\ \/ \A m \in S : m.maxVBal = -1
                  \/ \E c \in 0..(b-1) :
                        /\ \A m \in S : m.maxVBal =< c
                        /\ \E m \in S : /\ m.maxVBal = c
                                        /\ m.maxVal = v
       /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>
```
-/

action Phase2a (b : ballot) {
  require b ≠ tot.none
  -- ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
  require ∀ V, ¬ two_a b V
  -- \E Q \in Quorums, v \in Values
  let Q : quorum ← pick
  let v : value ← pick
  -- \A a \in Q : \E m \in S : m.acc = a (where S is 1b messages for ballot b)
  require ∀ n, member n Q → ∃ maxVBal' v', one_b n b maxVBal' v'

  -- Find the highest maxVBal among the 1b messages from Q
  -- Either all report -1 (no prior votes), or pick the max
  let maxVBalInQuorum : ballot ← pick
  let valueAtMax : value ← pick

  require (
    -- Case 1: \A m \in S : m.maxVBal = -1 (no one has voted)
    (maxVBalInQuorum = tot.none ∧
      ∀ n maxV v', member n Q → one_b n b maxV v' → maxV = tot.none) ∨
    -- Case 2: \E c : \A m \in S : m.maxVBal =< c /\ \E m \in S : m.maxVBal = c /\ m.maxVal = v
    (maxVBalInQuorum ≠ tot.none ∧
      -- Someone in Q reported maxVBalInQuorum with valueAtMax
      (∃ n, member n Q ∧ one_b n b maxVBalInQuorum valueAtMax) ∧
      -- All 1b messages from Q have maxVBal ≤ maxVBalInQuorum
      (∀ n maxV v', member n Q → one_b n b maxV v' → maxV ≠ tot.none → tot.le maxV maxVBalInQuorum) ∧
      -- The proposed value must be valueAtMax
      v = valueAtMax)
  )
  -- Send([type |-> "2a", bal |-> b, val |-> v])
  two_a b v := true
}

/-!
### Phase 2b: Acceptor votes for proposal

TLA+:
```
Phase2b(a) ==
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= maxBal[a]
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
```
-/

action Phase2b (a : node) {
  -- \E m \in msgs : m.type = "2a" /\ m.bal >= maxBal[a]
  let b : ballot ← pick
  let v : value ← pick
  require two_a b v
  require ge b (maxBal a)
  -- Send([type |-> "2b", bal |-> b, val |-> v, acc |-> a])
  two_b a b v := true
  -- maxVBal' = [maxVBal EXCEPT ![a] = b]
  maxVBal a := b
  -- maxBal' = [maxBal EXCEPT ![a] = b]
  maxBal a := b
  -- maxVal' = [maxVal EXCEPT ![a] = v]
  maxVal a := v
}

/-!
## Ghost Relations (TLA+-style)
-/

-- VotedForIn(a, v, b) == \E m \in msgs : m.type = "2b" /\ m.val = v /\ m.bal = b /\ m.acc = a
ghost relation VotedForIn (a : node) (v : value) (b : ballot) :=
  two_b a b v

-- WontVoteIn(a, b) == (\A v : ~ VotedForIn(a, v, b)) /\ maxBal[a] > b
ghost relation WontVoteIn (a : node) (b : ballot) :=
  (∀ v, ¬ VotedForIn a v b) ∧ gt (maxBal a) b

-- SafeAt(v, b) == \A c \in 0..(b-1) : \E Q \in Quorums : \A a \in Q : VotedForIn(a,v,c) \/ WontVoteIn(a,c)
ghost relation SafeAt (v : value) (b : ballot) :=
  ∀ c, lt c b → c ≠ tot.none →
    ∃ Q, ∀ a, member a Q → (VotedForIn a v c ∨ WontVoteIn a c)

-- ChosenIn(v, b) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b)
ghost relation ChosenIn (v : value) (b : ballot) :=
  ∃ Q, ∀ a, member a Q → VotedForIn a v b

-- Chosen(v) == \E b \in Ballots : ChosenIn(v, b)
ghost relation Chosen (v : value) :=
  ∃ b, ChosenIn v b

/-!
## Safety Property

TLA+: `Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)`
-/

safety [Consistency] ∀ v1 v2, Chosen v1 → Chosen v2 → v1 = v2

/-!
## Type Invariant

TLA+: `TypeOK == ... /\ \A a \in Acceptors : maxBal[a] >= maxVBal[a]`
-/

invariant [TypeOK] ∀ a, ge (maxBal a) (maxVBal a)

/-!
## Message Invariants

These correspond to TLA+'s MsgInv, split by message type.
-/

-- MsgInv for 1b messages
invariant [MsgInv1b] ∀ n b maxV v, one_b n b maxV v →
  -- m.bal <= maxBal[m.acc]
  tot.le b (maxBal n) ∧
  -- Either voted at maxVBal or maxVBal = -1
  ((maxV ≠ tot.none ∧ VotedForIn n v maxV) ∨ maxV = tot.none) ∧
  -- No votes between maxVBal and bal
  (∀ c, lt maxV c → lt c b → ∀ v', ¬ VotedForIn n v' c)

-- MsgInv for 2a messages
invariant [MsgInv2a] ∀ b v, two_a b v →
  -- SafeAt(m.val, m.bal)
  SafeAt v b ∧
  -- Unique 2a per ballot
  (∀ v', two_a b v' → v' = v)

-- MsgInv for 2b messages
invariant [MsgInv2b] ∀ n b v, two_b n b v →
  -- There exists a 2a with same ballot and value
  two_a b v ∧
  -- m.bal <= maxVBal[m.acc]
  tot.le b (maxVBal n)

-- 2a messages only exist at valid ballots (not none)
invariant [two_a_valid_ballot] ∀ b v, two_a b v → b ≠ tot.none

/-!
## Acceptor Invariant

TLA+'s AccInv
-/

invariant [AccInv] ∀ a,
  -- maxVBal[a] <= maxBal[a]
  tot.le (maxVBal a) (maxBal a) ∧
  -- (maxVBal[a] >= 0) => VotedForIn(a, maxVal[a], maxVBal[a])
  (maxVBal a ≠ tot.none → VotedForIn a (maxVal a) (maxVBal a)) ∧
  -- For all c > maxVBal[a], no vote exists
  (∀ c, gt c (maxVBal a) → ∀ v, ¬ VotedForIn a v c)

/-!
## Derived Lemmas (as invariants)

These correspond to TLA+'s VotedInv and VotedOnce lemmas.
-/

-- VotedInv: MsgInv /\ TypeOK => VotedForIn(a,v,b) => SafeAt(v,b) /\ b <= maxVBal[a]
invariant [VotedInv] ∀ a v b, VotedForIn a v b →
  SafeAt v b ∧ tot.le b (maxVBal a)

-- VotedOnce: MsgInv => VotedForIn(a1,v1,b) /\ VotedForIn(a2,v2,b) => v1 = v2
invariant [VotedOnce] ∀ a1 a2 b v1 v2,
  VotedForIn a1 v1 b → VotedForIn a2 v2 b → v1 = v2

#gen_spec

-- Note: Verification may timeout due to ∀∃∀ quantifier alternation in SafeAt
#time #check_invariants

#model_check
{
  node := Fin 3,    -- 3 acceptors (a0, a1, a2)
  value := Fin 2,   -- 2 values (v0, v1)
  quorum := Fin 3,  -- 3 majority quorums
  ballot := Fin 4   -- 0 = none, 1, 2, 3 = valid ballots (matches TLA+ MaxBallot = 2)
}
{
  -- Quorum membership: each quorum is a majority (2 of 3 nodes)
  -- Quorum 0: {node 0, node 1}
  -- Quorum 1: {node 0, node 2}
  -- Quorum 2: {node 1, node 2}
  member := fun n q =>
    match n.val, q.val with
    | 0, 0 => true  -- node 0 in quorum 0
    | 1, 0 => true  -- node 1 in quorum 0
    | 0, 1 => true  -- node 0 in quorum 1
    | 2, 1 => true  -- node 2 in quorum 1
    | 1, 2 => true  -- node 1 in quorum 2
    | 2, 2 => true  -- node 2 in quorum 2
    | _, _ => false
}

end PaxosTLAStyle
