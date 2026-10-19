#!/usr/bin/env python3
"""Inventory every model-bearing Examples file and choose a meaningful BMC query."""
import argparse
import hashlib
import json
from pathlib import Path
import re

# path: (query predicate, kind, source location/reason, compatibility notes)
QUERIES = {
 'AWS/AWSBuggy': ('dns_valid = false', 'safety_violation', 'DnsConsistent safety, line132', 'Buggy DNS race variant; same Veil namespace as AWSFixed and TLA/AWSDnsRace.'),
 'AWS/AWSFixed': ('dns_valid = false', 'safety_violation', 'DnsConsistent safety, line125', 'Repaired DNS race variant; include separately from AWSBuggy.'),
 'Ivy/Blockchain': ('¬ (∀ n1 n2 n b t tr t1 t2, (((honest n1 ∧ honest n2) → ((block_confirmed n1 b t ∧ block_confirmed n2 b t) ∨ (¬ block_confirmed n1 b t ∧ ¬ block_confirmed n2 b t))) ∧ ((honest n1 ∧ honest n2) → ((transaction_confirmed tr n1 ∧ transaction_confirmed tr n2) ∨ (¬ transaction_confirmed tr n1 ∧ ¬ transaction_confirmed tr n2))) ∧ ((honest n ∧ leader n t2 ∧ transaction_time tr t1 ∧ tot.le t1 t2 ∧ broadcasted n ∧ honest n1) → transaction_confirmed tr n1)))', 'safety_violation', 'Entire combined safety declaration, lines87–90', 'Negates all three conjuncts together and explicitly binds every source autoimplicit variable.'),
 'Ivy/ChordRingMaintenance': ('∃ n, error n', 'safety_violation', 'no_error safety, line143', ''),
 'Ivy/DecentralizedLock': ('∃ x y, has_lock x ∧ has_lock y ∧ x ≠ y', 'safety_violation', 'mutex safety, line51', ''),
 'Ivy/MultiSigAll': ('∃ n k v d, cancelled n k v d ∧ ¬ expired d', 'safety_violation', 'cancelled_after_deadline safety, line78', 'Five sorts and high-arity relations; distinct query from the earlier paid-tuple reachability experiment.'),
 'Ivy/MultiSigMajority': ('∃ n k v d, cancelled n k v d ∧ ¬ expired d', 'safety_violation', 'cancelled_after_deadline safety, line88', 'Quorum-based variant, distinct from MultiSigAll.'),
 'Ivy/NOPaxos': ('∃ s v1 v2, gh_committed s v1 ∧ gh_committed s v2 ∧ v1 ≠ v2', 'safety_violation', 'consistency safety, line243', 'Relational Ivy model; distinct from the collection-based TLA/NOPaxos.'),
 'Ivy/PaxosEPR': ('∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2', 'safety_violation', 'coherence safety, line91', ''),
 'Ivy/PaxosFirstOrder': ('∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2', 'safety_violation', 'coherence safety, line99', 'Distinct first-order variant of PaxosEPR.'),
 'Ivy/ReliableBroadcast': ('∃ src dst r v, ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v ∧ ¬ (sent src r ∧ initial_value src r v)', 'safety_violation', 'vote_integrity safety, lines122–124', 'Full Byzantine/round-indexed model; distinct from Simulate/ReliableBroadcast.'),
 'Ivy/RicartAgrawala': ('∃ n1 n2, holds n1 ∧ holds n2 ∧ n1 ≠ n2', 'safety_violation', 'mutual_exclusion safety, line51', ''),
 'Ivy/Ring': ('∃ n1 n2, n1 ≠ n2 ∧ leader n1 ∧ leader n2', 'existing_safety_violation', 'Existing unsat trace, lines57–60; single_leader safety, line42', 'Relational ring; overlaps Tutorial/Ring and POPL26/RingDec. Prefix explicitly sets veil.smt.trust=false.'),
 'Ivy/SuzukiKasami': ('∃ n m, crit n ∧ crit m ∧ n ≠ m', 'invariant_violation', 'mutex invariant, line111', 'No safety declaration; select the named mutex invariant.'),
 'Ivy/TwoPhaseCommit': ('¬ (∀ n n2, (decide_commit n → ¬ decide_abort n2) ∧ (decide_commit n → vote_yes n2) ∧ (decide_abort n → abort_flag))', 'safety_violation', 'Entire combined safety declaration, lines85–87', 'Negates all three conjuncts: commit/abort agreement, unanimous yes votes on commit, and abort-flag consistency.'),
 'Ivy/VerticalPaxosFirstOrder': ('∃ n1 r1 v1 n2 r2 v2, decision n1 r1 v1 ∧ decision n2 r2 v2 ∧ v1 ≠ v2', 'safety_violation', 'coherence safety, line132', 'Post-#gen_spec manual proof section is excluded; all model/invariant declarations are retained.'),
 'Puzzles/DieHard': ('big = 4', 'puzzle_reachability', 'Negation of not_solved invariant, line59', 'Uses the puzzle objective rather than the structural jug-capacity invariant.'),
 'Puzzles/Prisoners': ('Done ∧ ∃ p, p ≠ Counter ∧ timesSwitched p = 0', 'safety_violation', 'Safety declaration, line85', 'Concrete cardPrisoner=4 from #model_check is not imposed; symbolic theory parameters remain general.'),
 'Puzzles/RiverCrossing': ('goat_pos = far ∧ wolf_pos = far ∧ cabbage_pos = far ∧ farmer_pos = far', 'puzzle_reachability', 'Negation of unsolved invariant, line81', 'Uses the puzzle objective; retains action safety guards.'),
 'Simulate/CheckpointLeaseFailover': ('∃ l expiry now, checkpointed_until l expiry ∧ current_epoch now ∧ epochOrd.le expiry now ∧ active_on_leader l', 'safety_violation', 'checkpointed_expiry_respected safety, lines77–80', 'Designed for simulation, but retained to expose symbolic-backend limitations.'),
 'Simulate/LeaseKeepaliveRace': ('∃ c k, keepalive_succeeded c ∧ key_attached c k ∧ ¬ key_present k', 'safety_violation', 'renewal_keeps_keys_live safety, lines73–74', 'Designed for simulation; no concrete client/key domain bounds are imported.'),
 'Simulate/ReliableBroadcast': ('∃ n1 n2 v1 v2, delivered n1 v1 ∧ delivered n2 v2 ∧ v1 ≠ v2', 'safety_violation', 'agreement safety, lines61–62', 'Simplified simulation model, distinct from Ivy/ReliableBroadcast.'),
 'StellarConsensus/SCP': ('∃ n1 n2 b1 b2 v1 v2, intertwined n1 ∧ intertwined n2 ∧ confirmed_committed n1 b1 v1 ∧ confirmed_committed n2 b2 v2 ∧ v1 ≠ v2', 'safety_violation', 'intertwined_safe safety, lines218–220', 'Requires prebuilt Examples.StellarConsensus.SCPTheory; manual proof section after #gen_spec is excluded.'),
 'Synchronous/FasterFloodSet': ('∃ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 ∧ v1 ≠ v2', 'safety_violation', 'agreement safety, lines179–180', 'Optimized collection-based FloodSet variant; same namespace as other FloodSet files, isolated process required.'),
 'Synchronous/FloodSet': ('∃ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 ∧ v1 ≠ v2', 'safety_violation', 'agreement safety, lines137–138', 'Contains genuine function-valued delivery choices.'),
 'TLA/AWSDnsRace': ('current_plan > 0 ∧ plan_deleted current_plan true', 'invariant_violation', 'NeverDeleteActive invariant, line89', 'Finite-enum/Fin-based DNS race model; distinct from both AWS variants.'),
 'TLA/Bakery': ('∃ i j, i ≠ j ∧ pc i = cs ∧ pc j = cs', 'safety_violation', 'mutual_exclusion safety, line192', ''),
 'TLA/BcastByz': ('∃ p, isCorrect p ∧ pc p = AC', 'derived_reachability', 'PCState.AC and protocol step actions; no declared protocol safety property', 'Uses correct-process acceptance, rather than the static partition/cardinality sanity invariants. Contains collections and an Enumeration parameter.'),
 'TLA/BuggyCircularBuffer': ('count > BUFFER_SIZE', 'safety_violation', 'Safety declaration, line58', ''),
 'TLA/EPaxos': ('∃ i, commitSet.count (committedMap i) > 1', 'invariant_violation', 'Consistency invariant, lines1378–1379', 'Large collection/message model. Keep backend/elaboration failures as outcomes; do not replace its query with True.'),
 'TLA/EWD840': ('terminationDetected ∧ ¬ terminated', 'invariant_violation', 'TerminationDetection invariant, line103', 'Uses earlier ghost definitions; Fin domain size is a symbolic Nat parameter.'),
 'TLA/German': ('¬ (∀ i j, i ≠ j → (((cache i).state = cE → (cache j).state = cI) ∧ ((cache i).state = cS → ((cache j).state = cI ∨ (cache j).state = cS))))', 'invariant_violation', 'ctrlProp invariant, lines197–200', 'Explicitly binds the autoimplicit I/J variables from the source invariant.'),
 'TLA/KVSnap': ('¬ serialization', 'safety_violation', 'Serialization safety, line277; ghost serialization, lines273–275', 'Retains CC definitions and Veil.Util.Permutations import. Serialization uses enumerations, lists and permutations; backend support is not assumed.'),
 'TLA/KeyValueStore': ('¬ (snapshot_isolation ∧ transaction_cleanup)', 'invariant_violation', 'Txlifecycle invariant, line159', 'Both ghost predicates are defined before #gen_spec. Uses partial functions and sets.'),
 'TLA/MultiPaxos': ('∃ v1 v2 s, Chosen v1 s ∧ Chosen v2 s ∧ v1 ≠ v2', 'invariant_violation', 'consistency invariant, lines346–347', 'Uses earlier Chosen ghost predicate and collection-backed messages.'),
 'TLA/MutexViolation': ('∃ i j, i ≠ j ∧ pc i = cs ∧ pc j = cs', 'invariant_violation', 'mutual_exclusion invariant, line313', 'Contains list-valued call stacks; symbolic translation may be unsupported independently of the optimization.'),
 'TLA/NOPaxos': ('¬ Linearizability', 'invariant_violation', 'linearizability invariant, line944; ghost predicate, line316', 'Large collection/list/array model. Prefix sets veil.deferVCGeneration=true and maxHeartbeats=1600000.'),
 'TLA/Paxos': ('∃ v1 v2, Chosen v1 ∧ Chosen v2 ∧ v1 ≠ v2', 'invariant_violation', 'Consistency invariant, line298', 'Uses earlier Chosen ghost predicate and bounded ballot datatype.'),
 'TLA/Peterson': ('∃ i j, i ≠ j ∧ lockcs i ∧ lockcs j', 'safety_violation', 'mutual_exclusion safety, lines108–109', 'lockcs is defined before #gen_spec; finite process/control enums.'),
 'TLA/Raft': ('∃ i j, i ≠ j ∧ currentTerm i = currentTerm j ∧ pcState i Leader ∧ pcState j Leader', 'documented_safety_violation', 'BothLeader/MoreThanOneLeader specification comments, lines1059–1066', 'No active safety/invariant declaration. Tests the documented election-safety condition. Retains source-specific large heartbeat/typeclass limits.'),
 'TLA/Room': ('∃ r g1 g2, guestTset.contains g1 (registered r) ∧ guestTset.contains g2 (registered r) ∧ g1 ≠ g2', 'safety_violation', 'registered_at_most_one safety, lines122–123', 'Collection-based hotel key model.'),
 'TLA/SimpleAllocator': ('¬ (∀ c1 c2 : client, c1 ≠ c2 → resSet.isEmpty (resSet.intersection (alloc c1) (alloc c2)))', 'invariant_violation', 'resource_mutex invariant, line83', 'Negates the exact declared predicate; do not replace it by elementwise membership, since the abstract TSet class does not state an intersection-membership law.'),
 'TLA/Traffic': ('at_light = false', 'puzzle_reachability', 'Negation of puzzle_unsolvable safety, lines70–72', 'Reaches the intended puzzle goal: the car leaves the light.'),
 'TLA/TwoPhaseCommit': ('∃ rm1 rm2, (rmState rm1 == committed) ∧ (rmState rm2 == aborted)', 'invariant_violation', 'TCConsistency invariant, lines219–220', 'Distinct finite-control-state model from Ivy/TwoPhaseCommit; preserves the original Bool equality predicate.'),
 'Tutorial/FloodSet': ('¬ (∀ n1 n2 v1 v2, decision n1 v1 ∧ decision n2 v2 → v1 = v2)', 'existing_safety_violation', 'Existing agreement_violation trace, lines392–395', 'Tutorial variant overlaps Synchronous/FloodSet but is retained as its own model-bearing file.'),
 'Tutorial/POPL26/RingDec': ('∃ n1 n2, n1 ≠ n2 ∧ leader n1 ∧ leader n2', 'existing_safety_violation', 'Existing unsat trace, lines56–59', 'Near-duplicate relational Ring teaching variant, intentionally retained for complete file coverage.'),
 'Tutorial/POPL26/RingFin': ('leader.length > 1', 'safety_violation', 'single_leader safety, line53', 'List-based concrete implementation over a symbolic node type; distinct from relational Ring. No concrete nextNode/topology assignment is imported.'),
 'Tutorial/POPL26/RingNat': ('leader.length > 1', 'safety_violation', 'single_leader safety, line50', 'List-based Nat implementation. Concrete allNodes/nextNode values from #model_check are intentionally not imposed.'),
 'Tutorial/Ring': ('∃ l1 l2, leader l1 ∧ leader l2 ∧ l1 ≠ l2', 'safety_violation', 'single_leader safety, line217', 'Tutorial relational Ring, retained separately from Ivy/Ring and POPL26/RingDec.'),
}


def strip_comments(text):
    """Strip nested Lean block/line comments while preserving line numbers."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; out.append('  '); i += 2
            elif text.startswith('-/', i):
                depth -= 1; out.append('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                out.append(text[i+1]); i += 2
            else:
                if text[i] == '"': string = False
                i += 1
        elif text.startswith('/-', i):
            depth = 1; out.append('  '); i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out.append(' ' * (end-i)); i = end
        else:
            if text[i] == '"': string = True
            out.append(text[i]); i += 1
    if depth: raise ValueError('unterminated block comment')
    return ''.join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    repo, output = args.repo.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    rows, exclusions = [], []
    seen = set()
    for path in sorted((repo / 'Examples').rglob('*.lean')):
        rel = path.relative_to(repo)
        text = path.read_text()
        clean = strip_comments(text)
        module = re.search(r'^[ \t]*veil module ([\w.]+)', clean, re.M)
        if module is None:
            exclusions.append(dict(path=str(rel), reason='Support-only file: no veil module declaration; retained as an import dependency where needed.'))
            continue
        key = str(path.relative_to(repo / 'Examples').with_suffix(''))
        predicate, kind, query_source, notes = QUERIES[key]
        seen.add(key)
        boundary = re.search(r'^[ \t]*(?:#time[ \t]+)?#gen_spec\b', clean, re.M)
        if boundary is None: raise ValueError(f'no active #gen_spec: {path}')
        cut_line = clean[:boundary.start()].count('\n') + 1
        prefix_lines = clean.splitlines()[:cut_line-1]
        forbidden = [(i+1,l.strip()) for i,l in enumerate(prefix_lines) if re.match(r'^[ \t]*(?:#time[ \t]+)?(?:#model_check|#simulate|#check_invariants|#gen_executable|sat trace|unsat trace)\b',l)]
        if forbidden: raise ValueError(f'prior execution/verification commands in {path}: {forbidden}')
        options = [dict(line=i+1, directive=l.strip()) for i,l in enumerate(prefix_lines) if re.match(r'^[ \t]*set_option\b', l)]
        imports = [m[1] for m in re.finditer(r'^[ \t]*(?:public[ \t]+)?import[ \t]+([^\n]+)', '\n'.join(prefix_lines), re.M)]
        rows.append(dict(model=key.replace('/','_'), path=str(rel), module=module[1],
                         cut_line=cut_line, query=f'assert ({predicate})', query_kind=kind,
                         expected_status=None, query_source=query_source, notes=notes,
                         category=key.split('/')[0], source_options=options, imports=imports,
                         source_sha256=hashlib.sha256(text.encode()).hexdigest()))
    if set(QUERIES) != seen: raise ValueError(f'unmatched query entries: {set(QUERIES)-seen}')
    (output / 'manifest.json').write_text(json.dumps(rows, indent=2, ensure_ascii=False)+'\n')
    (output / 'exclusions.json').write_text(json.dumps(exclusions, indent=2)+'\n')
    print(json.dumps(dict(models=len(rows), excluded=len(exclusions), queries=len(QUERIES))))


if __name__ == '__main__':
    main()
