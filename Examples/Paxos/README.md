# Paxos Verification

This directory contains Veil specifications of the Paxos consensus protocol and
artifacts from an AI-assisted verification effort using Claude Code.

## Files

- **[`Paxos.lean`](Paxos.lean)** — TLA+-style Veil specification (set-based
  message encoding via `TSet`, function-based acceptor state). This is the
  *fixed* version, derived from [`Examples/TLA/Paxos.lean`](../TLA/Paxos.lean)
  (the original), with corrections identified during this process.
- **[`PaxosFOL.lean`](PaxosFOL.lean)** — Hybrid specification: Ivy-style
  relational state with TLA+-style ghost relations and invariants. Used as a
  validation vehicle to find the correct inductive invariant. Derived from
  [`Examples/Ivy/PaxosFOL.lean`](../Ivy/PaxosFOL.lean) (the original Ivy
  encoding).

## How This Was Developed

### Step 1. Failed direct proof of the TLA-style spec

We had a TLA+-style Veil encoding
([`Examples/TLA/Paxos.lean`](../TLA/Paxos.lean)) with the inductive invariant
ported from the
[TLAPS-checked proof](https://github.com/tlaplus/tlapm/blob/main/examples/paxos/Paxos.tla).
We asked Claude Code to prove the invariant interactively, but it failed. We
began to doubt whether the invariant was actually inductive in our encoding.

### Step 2. Creating the FOL specification

> **Prompt:** "Please refactor the `action`s in `Examples/Ivy/PaxosFOLSafeAt.lean`
> to more closely match the definitions in `Examples/TLA/Paxos.lean`. You should
> still keep the relational state definition, but otherwise make the actions more
> similar. Think deeply. The goal is to structure the protocols quite similarly
> such that we can have high confidence the invariants translate directly from
> the FOL version to the more TLA-style version."

Claude adapted [`Examples/Ivy/PaxosFOL.lean`](../Ivy/PaxosFOL.lean) to produce
[`PaxosFOL.lean`](PaxosFOL.lean) (see [differences below](#fol-spec-differences)).

### Step 3. Validating and fixing the invariant

> **Prompt:** "Let's start by model checking it. [...] come up with a
> `#model_check` call for `Examples/Ivy/PaxosFOLSafeAt.lean`"

`#model_check` confirmed the spec is not vacuous (decisions can be made) and
found no invariant violations. We also added a false invariant
(`∀ v, ¬ Chosen v`) to confirm the model checker finds a decision trace.

> **Prompt:** [User pasted a counterexample to induction from `#check_invariants`
> showing Phase2b does not preserve Consistency]

`#check_invariants` found the invariant was **not inductive**. The CTI had
`two_a` at ballot `tot.none` — an unreachable state not excluded by the
invariant. Claude discovered the missing clause:

```
invariant [two_a_valid_ballot] ∀ b v, two_a b v → b ≠ tot.none
```

> **Prompt:** "Let's now port the invariants into `Examples/TLA/PaxosFOLStyle.lean`
> and identify any potential discrepancies in the specifications."

Claude ported the invariant and identified key discrepancies between the
computational (TLA-style) and logical (FOL) encodings (see
[TLA spec changes below](#tla-spec-changes)).

> **Prompt:** "Try to identify any reasons we might be unable to prove the
> specification. Are there any discrepancies in the actions?"

Claude identified:
- Computational vs. logical encoding (`.any`/`.all`/`.filter` vs. `∃`/`∀`)
- Missing `validBallots_complete` assumption (connecting `validBallots` list to
  ballot validity)
- Missing `AcceptorsUNIV_complete` assumption (connecting `AcceptorsUNIV` list
  to universal quantification)
- `decide` wrapping issues
- Set operations (`TSet`) vs. bare relations

### Steps 4-5. Parallel proof effort

> **Prompt:** "Prove all 50 Paxos theorems in `Examples/Paxos/PaxosProof/*.lean`
> by spawning parallel sub-agents. Each theorem file currently has `placeholder` in the
> proof — replace with complete proofs (no `incomplete marker` allowed)."

Each VC was split into its own file in [`Examples/Paxos/PaxosProof/`](../TLA/PaxosProof/).
Claude Code first proved them sequentially (too slow), then we instructed it to
spawn parallel sub-agents (one per theorem file). This succeeded for 49 of 50
theorems.

### Step 6. Hardest proof: `Phase2a_MsgInv2a`

> **Prompt:** "The only remaining unproven theorem is
> `Examples/Paxos/PaxosProof/Phase2a_MsgInv2a.lean`. Your goal is to prove this
> theorem. [...] This seems like it might be a difficult proof, so plan ahead."

Claude initially attempted an inductive argument over ballot numbers and got
stuck in a loop. The key human guidance was:

> **Prompt:** "It seems you're going in loops. You shouldn't need an inductive
> argument over ballot numbers — it should be able to prove the goal only by
> using the existing invariants and quorum intersection, without further
> induction."

The correct high-level argument (found via web search for "paxos 2a correctness
argument"):
1. If all 1b messages report `maxVBal = none`: every quorum member promises not
   to vote at any ballot < b, so `WontVoteIn` holds for all c < b.
2. Otherwise, let `maxMsg` be the 1b with the highest `maxVBal`:
   - For c > maxMsg.maxVBal: use quorum Q; `MsgInv1b` interval property gives
     `WontVoteIn`.
   - For c = maxMsg.maxVBal: use quorum Q; `VotedOnce` ensures all votes at
     that ballot agree on v.
   - For c < maxMsg.maxVBal: `VotedInv` gives `SafeAt(v, maxMsg.maxVBal)`;
     reuse its witness quorum Q'.

During this proof, `validBallots_complete` was corrected from an implication
(`→`) to an equivalence (`↔`), which was needed to derive `b ≠ tot.none` from
`b ∈ validBallots`.

## Conversation Transcripts

- [`2-Port-Spec-to-FOL/`](2-Port-Spec-to-FOL/) — Step 2: comparing Ivy and
  TLA+ invariants, creating the hybrid FOL spec
- [`3-Find-FOL-Invariant-and-Port-Back/`](3-Find-FOL-Invariant-and-Port-Back/)
  — Step 3: model checking, CTI analysis, porting invariants back
- [`5-Proof-Attempt/`](5-Proof-Attempt/) — Steps 4-5: initial (interrupted)
  proof attempts
- [`6-Hardest-Proof-With-Guidance/`](6-Hardest-Proof-With-Guidance/) — Step 6:
  proving `Phase2a_MsgInv2a` (216 messages, 3 context compactions)

<a id="fol-spec-differences"></a>
## Key Differences: `PaxosFOL.lean` vs `Examples/Ivy/PaxosFOL.lean`

The original Ivy encoding and the hybrid FOL encoding differ significantly:

| Aspect | Ivy (`Examples/Ivy/PaxosFOL.lean`) | Hybrid FOL (`PaxosFOL.lean`) |
|--------|-------------------------------------|------------------------------|
| Types | `node`, `value`, `quorum`, `round` | `node`, `value`, `quorum`, `ballot` |
| Order | `TotalOrder` + explicit `none` individual | `TotalOrderWithZeroAndNone` (built-in `none` and `zero`) |
| Message relations | `one_b_max_vote`, `proposal`, `vote`, `decision` | `one_b`, `two_a`, `two_b` (no `decision`) |
| Acceptor state | None (implicit in message history) | Explicit `maxBal`, `maxVBal`, `maxVal` functions |
| Action names | `send_1a`, `join_round`, `propose`, `cast_vote`, `decide` | `Phase1a`, `Phase1b`, `Phase2a`, `Phase2b` |
| Ghost relations | None | `VotedForIn`, `WontVoteIn`, `SafeAt`, `ChosenIn`, `Chosen` |
| Safety property | `coherence` via explicit `decision` relation | `Consistency` via ghost `Chosen` predicate |
| Invariant style | EPR-friendly (`choosable_proposal`, `one_b_max_vote_properties1/2/3`) | TLA+-style (`MsgInv1b/2a/2b`, `AccInv`, `VotedInv`, `VotedOnce`) |

<a id="tla-spec-changes"></a>
## Key Changes: `Examples/TLA/Paxos.lean` → `Paxos.lean`

Changes made to the TLA-style specification during the verification process:

| Change | Old (`Examples/TLA/Paxos.lean`) | Fixed (`Paxos.lean`) |
|--------|-------------------------------|----------------------|
| Ballot order | `TotalOrderWithZero` + separate `minusOne : ballot` | `TotalOrderWithZeroAndNone` (built-in `none`) |
| `VotedForIn` | Subtype `∃ (m : { m // m ∈ msgs }), ...` | Explicit `∃ m, msgTset.contains m msgs ∧ ...` |
| `SafeAt` | Commented out; missing `c ≠ tot.none` guard | Defined; includes `c ≠ tot.none` guard |
| `WontVoteIn` | Commented out | Defined |
| Invariants | Only `Consistency` | Full set: `TypeOK`, `MsgInv1b/2a/2b`, `AccInv`, `VotedInv`, `VotedOnce`, `two_a_valid_ballot` |
| Safety | `invariant [Consistency] ∀ v1 v2, Chosen v1 ∧ Chosen v2 → v1 = v2` | `safety [Consistency] ∀ v1 v2, Chosen v1 → Chosen v2 → v1 = v2` |
| Assumptions | Only `quorum_intersection` | Added `AcceptorsUNIV_complete`, `validBallots_complete` (as `↔`) |
| Phase2a guard | None | Added guard on selected acceptors (see below) |
| `decide` usage | `decide $ m.msgType = ...` (propositional) | `m.msgType == ...` (boolean) in some places |

### Phase2a selected-acceptor guard

In the TLA+ original, `Phase2a` picks `S` directly from
`SUBSET {m ∈ msgs : m.type = "1b" ∧ m.bal = b}`, so every element of `S` is a
real 1b message by construction. The Veil spec optimizes for faster model
checking by picking a set of *acceptors* instead of a set of *messages*
(reducing non-determinism from 2^|msgs| to 2^|acceptors|), then constructing `S`
by filtering messages to only those from selected acceptors:

```lean
let selectedAcceptors ← pick AcceptorSet
let S := msgTset.filter all1bMsgs (fun m => acSet.contains m.acc selectedAcceptors)
```

The original code had this filter but not the guard below. The problem is that
`selectedAcceptors` could include acceptors with no 1b for this ballot — the
filter would simply produce no messages for them, and the downstream quorum
coverage check would reject such cases anyway. But this wastes model checking
time exploring dead-end branches. The fix adds an explicit guard that prunes
these early:

```lean
require (acSet.toList selectedAcceptors).all (fun a =>
    (msgTset.toList all1bMsgs).any (fun m => decide (m.acc = a)))
```

The guard and filter work in opposite directions: the guard ensures every
selected acceptor has at least one 1b
(`selectedAcceptors ⊆ {a | ∃ m ∈ 1b_msgs, m.acc = a}`), while the filter
restricts messages to selected acceptors
(`S = {m ∈ 1b_msgs | m.acc ∈ selectedAcceptors}`).
