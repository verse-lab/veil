# Paxos Proof Parallelization - Instructions for Main Agent

## Task Overview

Prove all 50 Paxos theorems in `Examples/Paxos/PaxosProof/*.lean` (excluding `Spec.lean`) by spawning parallel sub-agents. Each theorem file currently has `placeholder` in the proof - replace with complete proofs (no `incomplete marker` allowed). The specification is in @Examples/Paxos/PaxosProof/Spec.lean  .

## Workflow

### 1. Identify Failing Proofs

```bash
python scripts/build-paxos-proofs.py
```

This shows a matrix of ✓/✗ for each action×invariant combination and [PASS] / [FAIL] for each theorem individual file.

### 2. Spawn Sub-Agents in Parallel

For each failing theorem file, spawn a **general-purpose** agent with this task:

```
Prove the theorem in Examples/Paxos/PaxosProof/<TheoremName>.lean

The file currently contains `placeholder` in the proof. Your goal:
1. Replace `placeholder` with a complete proof (NO `incomplete marker` - forbidden)
2. Build with: python scripts/build-paxos-proofs.py Examples/Paxos/PaxosProof/<TheoremName>.lean
3. Iterate until it compiles successfully

Context:
- Spec: Examples/Paxos/PaxosProof/Spec.lean (Paxos protocol definition)
- Reference: Examples/TLA/PaxosFOLStyle.lean (original monolithic proofs)
- Patterns: Examples/TLA/Paxos.lean (similar protocol, different invariants)

Proof structure:
- Use `unveil` tactic to intro hypotheses
- Extract pre-state invariants from `hinv` with `obtain`
- Use system assumptions `has` (quorum intersection, etc.)
- Common patterns:
  * Simple preservation: state unchanged → invariant holds
  * Message insertion: new message differs → old messages satisfy invariant
  * TSet operations: use axioms from Veil/Frontend/Std.lean

If TSet axioms are insufficient, you MAY add new axioms to the `TSet` class in Veil/Frontend/Std.lean, but you MUST also provide proofs in the instance definitions.

It is not helpful to include comments in the Lean proofs you generate. They often confuse more than help. Do your best to avoid them.

Key definitions (from Spec.lean):
- VotedForIn, ChosenIn, Chosen, WontVoteIn, SafeAt
- Ballot relations: lt, gt, ge (defined via tot.le)
- Actions: Phase1a, Phase1b, Phase2a, Phase2b, initializer
- Invariants: TypeOK, MsgInv1b, MsgInv2a, MsgInv2b, AccInv, VotedInv, VotedOnce, two_a_valid_ballot, Consistency
```

### 3. Launch Agents

Spawn agents in **batches** (e.g., 10 at a time) to manage resources:

- Use `Task` tool with `subagent_type="general-purpose"`
- Run in background: `run_in_background=true`
- Each agent works independently on one theorem file

### 4. Monitor Progress

Periodically check:

```bash
python scripts/build-paxos-proofs.py
```

Track which theorems are proven (✓) vs failing (✗).

### 5. Handle Difficult Proofs

If an agent struggles (>30min):

- Check its progress via the output file
- May need to provide hints about proof strategy
- Hardest proofs likely:
    - `Phase2a_MsgInv2a` (SafeAt for new proposals)
    - `Phase2b_Consistency` (main safety)
    - `Phase2b_VotedOnce` (agreement)

### 6. Final Verification

When all agents complete:

```bash
python scripts/build-paxos-proofs.py
```

Should show: **50 passed, 0 failed** with all ✓ in the matrix.

## Success Criteria

All 50 theorem files build successfully without `incomplete marker`.