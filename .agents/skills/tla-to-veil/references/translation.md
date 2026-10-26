# Translation traps and encoding choices

## Mapping at a glance

The first table maps TLA+ language constructs: declarations, data structures, actions, expressions, and properties. The second maps what specs commonly model with them, such as messages, networks, and sentinel values. In both, the Veil column gives the usual form. The Alternative column names another encoding and when to use it, and is filled only where clarity or state-space cost really differs. Notes are caveats and pointers to the sections below.

Example names in parentheses, such as `(Paxos)`, refer to files such as `Examples/TLA/Paxos.lean` in the Veil repository. Section links point to further explanations in this document. `ModelChecker-Guide` refers to Veil's `docs/ModelChecker-Guide.md`.

### Language constructs

| TLA+ | Veil | Alternative, and when | Notes |
| --- | --- | --- | --- |
| `CONSTANT` set of model values | `type node`, typically instantiated as `Fin k` | | See [Domains](#domains-bounds-and-arithmetic) before representing source sets that may share elements as separate Veil types. If the source also uses the set as a value, add a TSet constant ([Constants used as sets](#constants-used-as-sets)) |
| `CONSTANT` size used in types | `param n : Nat` | | Mind `0..N` vs. `1..N` |
| `CONSTANT` fixed value | `immutable individual c : T`, given in the theory argument | `param c : T`, given in the `Instantiation` argument, or `instantiate` a type class, whose instance Lean infers from the instantiation. The compiled checker calls either directly, which may be faster; a class also bundles the constant's assumptions (Paxos: `Membership`, checked with Veil's `Quorum` types) | For verification, all three are uninterpreted symbols constrained by the assumptions; see ModelChecker-Guide, "Constant Functions and Relations" |
| `ASSUME P` | `assumption [name] P` | | |
| `VARIABLE x` | `individual x : T` | | |
| `f ∈ [A → B]` | `function f : A → B` | `relation f : A → B → Bool`, when totality isn't needed, e.g. for deductive verification ([Functions as relations](#functions-as-relations)) | |
| A function whose support (`DOMAIN f`, the keys currently mapped to values) changes (`f @@ (k :> v)`) | A TMap field: `instantiate M : TMap K V MapT`, `individual f : MapT` | `relation f : K → V → Bool`, e.g. for deductive verification ([Functions as relations](#functions-as-relations)) | The key type `K` stays fixed. Quantify over the current support with `M.keys f` ([Quantifiers and set operations](#quantifiers-and-set-operations)) |
| `S ⊆ A`, `[A → BOOLEAN]` | `relation s : A → Bool` | A TSet carrier field, for set algebra, cardinality, or sets passed as values | |
| `[A → SUBSET B]` | `relation r : A → B → Bool` | A function into a TSet carrier, for set algebra | |
| `Cardinality`, `∪`, `∩`, `\`, `⊆`, `=` | TSet `count`, `union`, `intersection`, `diff`, `TSet.isSubset`, `=` | | `=` relies on a canonical carrier ([Quantifiers and set operations](#quantifiers-and-set-operations)) |
| `Max`, `Min`, or a sum over a set, defined by `CHOOSE` or recursion | `foldl` over `xSet.toList s` | | A computation, not a quantifier |
| Record, `[r EXCEPT !.f = v]` | `@[veil_decl] structure`, `{ r with f := v }` | | Don't add meaningless fields. A one-field record used only to wrap and read a value can use the field's type directly |
| Strings used as tags (`"idle"`, `"done"`) | `enum phase = {idle, done}` | | Use this enum only if the source tag is always `"idle"` or `"done"` in reachable states. If the source has an `OTHER` branch for other strings, explain in a comment why that branch can never run. |
| `Seq(S)` | `List S` | `fQueue S` for a FIFO queue, `Array S` for random access ([Sequences](#sequences)) | Keep order and duplicates, shift 1-based indices, never replace a sequence with a set |
| `Init` | `after_init` | | A field it doesn't assign starts at its default value ([Frames and initial states](#frames-and-initial-states)) |
| `x ∈ S` in `Init` | `let v :\| v ∈ S`, then `x := v`; `x := *` when `S` is all of `x`'s type | | Keep every allowed initial value, not one representative ([Frames and initial states](#frames-and-initial-states)) |
| Action in `Next` | `action` of the same name, the `∃` around it in `Next` as parameters | A local choice instead of a parameter, when that `∃` ranges over state (`\E m \in msgs`) or an awkward range (`-D..D`); see [Actions](#actions) | One Veil action per source action; see [Actions](#actions) |
| Operator used by actions | `procedure` (stateful), `ghost relation`/`ghost function` (pure) | A ghost predicate instead of a derived set that is only tested for membership (SimpleAllocator) | Never an `action`, which would add an enabled step |
| `ENABLED A` | `ghost relation` holding A's enabling conjuncts | | A uses it as its guard too |
| `LET x == e IN` | `let x := e` | | A local binding, not state |
| Guard conjunct | `require P` | | |
| `Assert(P, msg)` (PlusCal) | `assert P` | | When `P` is false, TLC stops with an error; Veil reports `assertion_failure` |
| `x' = e`, `[f EXCEPT ![i] = e]`, `[x ∈ A ↦ e]` | `x := e`, `f i := e`, `f X := e` | | See [Simultaneous updates](#simultaneous-updates) |
| `∃ m ∈ S : P(m) ∧ …` in an action's body | `let m : { m // m ∈ S } :\| P m` | An action parameter, when the `∃` is in `Next` around the action and ranges over a fixed domain ([Actions](#actions)) | See [Choice](#choice) |
| `∃ T ∈ SUBSET S : …` | `let t : { t // TSet.isSubset t s } :\| …` | | Every allowed subset, including the empty one if allowed |
| `INVARIANT`, `∀ x ∈ S : P` | `invariant [name]` / `safety`, `∀ x : { x // x ∈ S }, P x` | | Sequences, maps, intervals: see [Quantifiers and set operations](#quantifiers-and-set-operations) |
| `CONSTRAINT`, deadlock checking | `state_constraint`, `termination` | | They differ from TLC; see [Stuttering, deadlock, and constraints](#stuttering-deadlock-and-constraints) |
| Relation hard to sequentialize | `transition` | | Exact but slow to model-check; prefer an imperative action when the dependencies allow |

### Modeling patterns

| What the source models | Veil | Alternative, and when | Notes |
| --- | --- | --- | --- |
| Messages as records tagged by kind (`[type \|-> "1a", bal \|-> b]`) | `@[veil_decl] inductive`, one constructor per kind (Paxos) | | In a quantified guard, a `match` on the kind needs a `Bool` body ([Guards](#guards-assumptions-and-properties)) |
| A set of sent messages (`msgs' = msgs \cup {m}`) | A TSet field: `instantiate msgSet : TSet Msg MsgSet`, `individual msgs : MsgSet` (Paxos, NOPaxos) | Boolean fields or relations that record which messages are present: `msgCommit : Bool` means Commit is in the set; `msgPrepared r` means Prepared from `r` is in the set (TwoPhaseCommit) | Messages stay once sent; `\E m \in msgs : …` is a guard or a choice ([Choice](#choice)) |
| A bag of messages, where receiving consumes one copy (`Bags`, or counts in `[Msg -> Nat]`) | A TMultiset field, carrier `TMapMultiset` | | Only when multiplicity matters (ModelChecker-Guide, "Set-Valued State") |
| A FIFO channel (`Seq(Msg)` per link) | `fQueue Msg` per link | | See [Sequences](#sequences) |
| A value or a fresh `NoVal` (`NoVal == CHOOSE v : v \notin Values`) | `Option` | | Several sentinels need an explicit encoding |
| A numeric sentinel, such as ballot `-1` | A shift into a `Fin` (Paxos: `Fin (maxBallot + 2)`) | | Don't cast `-1` to `Nat` |
| A process set plus a distinguished process (`ProcSet == Clients \cup {Resizer}`) | One type, with the extra process as an `immutable individual` | A dedicated inductive type (CosmosDB) | |
| Quorums as a constant set with an intersection assumption (`CONSTANT Quorums`) | `type quorum` with `instantiate mem : Membership acceptor quorum`, checked with `quorum` instantiated as `Quorum`/`MinQuorum` (Paxos) | | Quorums defined by cardinality keep their definition ([Constants used as sets](#constants-used-as-sets), [Re-modeling](#re-modeling-is-a-separate-decision)) |
| PlusCal's `pc` and call stack | An `enum` of labels with `function pc : proc → label`; `function stack : proc → List Frame`, `Frame` a `structure` (MutexViolation) | | One action per label ([Actions](#actions)) |

## Mirror the source

Write each definition the way the source writes it, and add nothing the source lacks. A reviewer can then check the translation definition by definition ([validation.md](validation.md)). An equivalent form is fine where the literal one is unreadable or fails in Veil ([When Veil misbehaves](#when-veil-misbehaves)); say why in a comment.

### Actions

- Translate an `∃` inside an action as a local choice: `Apply == \E r \in RM : …` becomes `action Apply { let r : rm :| … }`. For a state-dependent set such as `msgs`, a local choice enumerates only its members, while an action parameter enumerates its whole type.
- Keep a source `IF` as `if`/`else` within one action. For a disjunction whose guards can both hold, choose nondeterministically. At `x = 0`, both branches below must remain possible:

  ```lean
  -- Source: (x <= 0 /\ x' = 1) \/ (x >= 0 /\ x' = 2)
  action Step {
    let left ← pick Bool
    if left then
      assume x ≤ 0
      x := 1
    else
      assume x ≥ 0
      x := 2
  }
  ```

  Use `assume` for each branch guard, so a false guard discards only that choice. A `require` can cause an assertion failure when a procedure calls the action ([Guards](#guards-assumptions-and-properties)).

  For `CASE`, use `if`/`else` when the guards are mutually exclusive. Preserve `OTHER`; if there is no `OTHER`, an unmatched case must still report an error.
- Compute values fixed by the current state with `let`; don't add a parameter and constrain it with `require`. For a computed 1-based index over a `Fin` domain, update pointwise: `logIndex O := if O.val + 1 = endOff then v else logIndex O`. Extra parameters change traces and make the checker enumerate unnecessary candidates.

### Constants used as sets

If the source uses a constant set in expressions such as `Cardinality(S)` or `SUBSET S`, add a TSet constant alongside its element type. Keep the source's set name and require the constant to contain every element of that type:

```lean
type acceptor
type AcceptorSet
instantiate acSet : TSet acceptor AcceptorSet
immutable individual acceptors : AcceptorSet
assumption [acceptors_complete] ∀ a : acceptor, a ∈ acceptors

-- #model_check { acceptor := Fin 3, AcceptorSet := OrdList _ }
--   { acceptors := OrdList.ofList (List.finRange 3) }
```

A `List` plus completeness and `Nodup` assumptions would make the constant ordered. Iterate with `acSet.toList acceptors`; see [Choice](#choice) for matching TLC's `CHOOSE`.

### Quantifiers and set operations

Write `\E` and `\A` as Lean quantifiers over the collection the source names, not as `toList` followed by `List.any`/`List.all` and `= true`. Here `xSet` and `M` stand for the names given in `instantiate`:

| TLA+ | Veil |
| --- | --- |
| `\E f \in files : P(f)`, where `files` is a TSet | `∃ f : { f // f ∈ files }, P f.val` |
| `\A c1, c2 \in committed : …` | `∀ c1 c2 : { c // c ∈ committed }, …` |
| `\E w \in Range(q) : …`, where `q` is a sequence | `∃ w ∈ q, …` |
| `{w \in Range(s) : P(w)} = {}` | `¬ ∃ w ∈ s, P w` |
| `{w \in Range(s) : P(w)} = {x}` | `(∃ w ∈ s, P w) ∧ ∀ w ∈ s, P w → w = x` |
| `\A k \in DOMAIN m : P(m[k])`, where `m` is a TMap | `∀ k ∈ M.keys m, P ((M.lookup k m).getD d)` |
| `\E k \in DOMAIN m : …` as a choice | `let k : { k // k ∈ M.keys m } :\| …` |
| `\A i \in 0..N : …` | `∀ i ≤ N, …` |
| `\E n \in 1..N` as a choice | `let n : { n // n ∈ List.range' 1 N } :\| …`; for `-D..D`, choose `o` from `List.range (2 * D + 1)` the same way and use `(o.val : Int) - D` |
| `\A i \in 1..Len(s) : P(i, s[i])` | `∀ e ∈ s.zipIdx, P (e.2 + 1) e.1` |
| `Len(s) > 0 => P(s[Len(s)])` | `∀ x ∈ s.getLast?, P x` |
| `S /= T`, `S = {}` | `s ≠ t`, `xSet.isEmpty s` |

- With a `Prop` body, `∃ f : { f // f ∈ files }, …` is decidable: Veil enumerates TSet members.
- Quantify over `DOMAIN m` when the source does, not over the values or the key-value pairs. For a TMap, go through its `keys` list; the `getD` default is then unreachable, which a comment should say. A ghost function can name a map read such as `auxObsSnapshots[lsn]`: `(M.lookup lsn m).getD xSet.empty`.
- `∃ v ∈ M.lookup k m, P v` quantifies over an `Option`. Where TLC would fail to evaluate `m[k]` because `k ∉ DOMAIN m`, this form makes the property fail instead, so the problem still surfaces.
- Use a canonical set encoding, such as a TSet with an `OrdList` carrier. A raw `List` distinguishes `[a, b]`, `[b, a]`, and `[a, a, b]`, even though they represent the same set, and can inflate state counts.
- TSet has no extensionality law, so `s = t` compares representations. That is exact for canonical carriers such as `OrdList`, which is what the model checker runs; in a deductive proof, `s ≠ t` and `¬ ∀ k, k ∈ s` need not coincide.

### Names and definitions

- Keep the source's names for constants, operators, and `LET` bindings, with one helper per source operator, even if two currently share a body.
- Keep intermediate definitions to make the translation easy to compare with the source.
- Choose helper parameter types that cover all values passed at every source call site.
- Drop a `LET` binding only if nothing uses it.

### Re-modeling is a separate decision

Preserve definitions from the source, including cardinality-based quorum predicates. Replacing such a predicate with an abstract quorum family requires a separate argument that the same behaviors are preserved.

## Examples to imitate

The tables already cite examples for common data encodings; German also shows record updates. Useful definitions to inspect:

- KeyValueStore `CloseTx`: simultaneous updates.
- Paxos `Phase1a`/`Phase1b`: existential guards and choices.
- EWD840 `after_init`: arbitrary initial state.
- BcastByz: `Stutter` for self-loops; guards checked after `Receive`.
- MultiPaxos `NewProposals`, NOPaxos `CombineLogs`: `CHOOSE` fixed to one rule.

Follow the common layout of quoting each TLA+ definition above its Veil translation. These are examples, not certified translations. Their `#model_check` instances may differ from the source cfg; compare every action with your selected source.

## Simultaneous updates

`x' = y /\ y' = x` is not `x := y` followed by `y := x`. Snapshot first:

```lean
let oldX := x
x := y
y := oldX
```

For each assignment, identify which values its right-hand side reads from old or new state, including reads inside helpers. Order assignments accordingly, saving old values when needed. Check guards on primed variables after the corresponding updates.

- In `[f EXCEPT ![i] = e]`, `@` is the old `f[i]`. Check for aliasing before splitting a multi-point `EXCEPT`.
- If the right-hand side of `f X := e` reads `f`, make sure it reads the old function; snapshot if unsure.

## Frames and initial states

Audit every variable in every action. Where TLA+ leaves a primed variable unconstrained, use `x := *`, `let v :| P`, or a `transition`; omitting the assignment would freeze it.

`after_init` starts from default values, so a field it doesn't assign gets a single value where TLA+ may allow many. Use `x := *` / `f := *` for arbitrary initial values (e.g. EWD840's `active ∈ [Node → BOOLEAN]`).

A variable chosen in `Init` and never changed is still state; turning it into a constant drops initial states.

## Guards, assumptions, and properties

- A `require` in an action invoked by the environment is an enabling condition. In a procedure called from an action, a false `require` is an assertion failure, so a branch that should merely be disabled shows up as a bug. Use `assume` for intended filtering inside helpers, or establish the condition in the caller.
- `assert` checks executions, `assume` discards them, `invariant`/`safety` checks reachable states. Don't swap them to make a counterexample disappear.
- `TypeOK`: drop only the conjuncts that Veil types already enforce; keep semantic ones such as `rcvd[p] ⊆ sent` as invariants. Likewise, `ASSUME N > 3*T` isn't enforced by `Nat`: state it as an `assumption` or check that the chosen parameters satisfy it.
- A quantified condition with a `Prop` body is decidable when its parts are, except for a `match`: make that body `Bool`-valued, e.g. `require ¬ ∃ m : { m // m ∈ msgs }, (match m.val with | .phase1a bal => decide (bal = b) | _ => false) = true` (Paxos `Phase1a`).

## Choice

1. `~∃ m ∈ S : P(m)` is a guard; no witness is needed.
2. `∃ m ∈ S : P(m) /\ Update(m)` must cover every witness. No witness means the step is disabled.
3. `CHOOSE x ∈ S : P(x)` is deterministic: same S and P, same value. With a unique witness, a relational choice is fine once existence and uniqueness are clear; otherwise fix one rule and state it. TLC picks by its own value order, so matching TLC's state graph exactly may require checking which value it picks; over a TSet constant, the carrier's order plays that role ([Constants used as sets](#constants-used-as-sets)). Don't turn the no-witness case into a disabled step or an invented default.

A `CHOOSE` that selects a unique index can use `findIdx`.

Narrowing a choice needs an argument that the same successors remain reachable; fewer witnesses alone isn't enough.

## Domains, bounds, and arithmetic

- Take bounds from the cfg and Veil instantiation: `0..N` has N+1 values, `1..N` has N. For 1-based IDs, `i : Fin n` represents `i.val + 1`.
- Before representing source sets as separate types, check for shared elements, equality comparisons across sets, and possible empty sets.
- `Fin` arithmetic wraps and `Nat` subtraction truncates; preserve the source guards that make these operations safe. For maxima of empty sets, preserve the source behavior instead of supplying a default.
- Fields may use unbounded types such as `Nat` or sequences, but complete checking needs a finite reachable state space and terminating enumeration in initialization, action parameters, and local choices.

## Sequences

A TLA+ sequence can become a `List`, an `Array`, or Veil's `fQueue` (in `Veil/Core/Tools/ModelChecker/Concrete/Containers.lean`). All three keep order and duplicates, and the model checker counts sequences with equal contents as one state, so the choice affects cost, not the state space. Choose by how the source adds and removes elements:

| How the source uses it | Veil | Cheap operations |
| --- | --- | --- |
| Stack: `<<x>> \o s`, `Head(s)`, `Tail(s)` (MutexViolation) | `List` | `x :: s`, `s.head!`, `s.tail` |
| Queue: `Append(s, x)`, `Head(s)`, `Tail(s)` (MutexViolation) | `fQueue` | `q.enqueue x`, `let (hd, tl) := q.dequeueD`, `q.isEmpty`, `q.size` |
| Random access: `s[i]`, `Len(s)` (NOPaxos) | `Array` | `a[i - 1]!`, `a.size` |

For `List`, `Append(s, x)` is `s ++ [x]`, `s \o t` is `s ++ t`, `[s EXCEPT ![i] = e]` is `s.set (i - 1) e`, `SubSeq(s, m, n)` is `(s.drop (m - 1)).take (n + 1 - m)`, `SelectSeq(s, P)` is `s.filter P`, and `Last(s)` is `s.getLast!`.

`s.Pairwise (fun a b => a ≤ b)` checks every earlier/later pair, matching `\A i, j \in DOMAIN s : i > j => s[i] >= s[j]`. Use `(s.map f).Nodup` for uniqueness of the mapped values and `s.zip s.tail` for adjacent pairs.

`List` length, indexing, and append are linear in the sequence length, as are `Tail` on an `Array` (`a.extract 1 a.size`) and materializing `q.toList`. Array writes such as `a.push x` and `a.set! (i - 1) e` may require a full copy when the search retains the old array.

These costs can be negligible for short sequences. If they dominate runtime on long sequences or inside quantifiers, explain the bottleneck before introducing a new container.

- `Head`/`Tail` of `<<>>` and an out-of-range `s[i]` are errors in TLC, while `head!`, `tail`, `[i]!`, and `dequeueD` return a value anyway. Keep the source's guard, or `assert` the condition where the source has none, so the error still shows.
- `fQueue` has no `DecidableEq`, and its `==` compares its internal front and back lists, so two queues with the same contents can differ. Compare and quantify over `q.toList` instead.

## Functions as relations

A TLA+ function can also be a relation, `relation f : A → B → Bool`, where `f a b` means `f[a] = b`. The relation drops totality, so it suits a function whose totality nothing depends on, and a partial one such as a map whose `DOMAIN` grows. It can make deductive verification easier: without a function symbol, quantified verification conditions avoid the function cycles that make SMT solvers diverge. Tamir et al. ([OOPSLA 2023](https://doi.org/10.1145/3622864)) treat every function this way and add totality back only where a proof needs it. For a module that is only model-checked, `function`, or a TMap for a partial function, is simpler.

Keep the relation a function:

- Update it as one: `f a X := X == v` also clears the old value. State that it has at most one value per argument as an invariant, e.g. `(f A B1 ∧ f A B2) → B1 = B2` (`ll_coherence` in `Examples/Ivy/NOPaxos.lean`).
- Read it with a choice, `let v :| f a v`. Where no value exists the step is disabled, whereas TLC reports an error for `f[a]` outside `DOMAIN f`; guard or `assert` existence where the source assumes it.

## Stuttering, deadlock, and constraints

- `[][Next]_vars` stuttering adds no distinct states. An explicit `UNCHANGED vars` disjunct becomes an empty action; it changes generated-state totals and deadlock detection, not distinct counts.
- TLC checks deadlock unless the cfg says `CHECK_DEADLOCK FALSE`; Veil reports none unless the module has a `termination` clause. `termination false` matches TLC's default; `termination P` accepts stuck states satisfying P and adds no self-loop.
- `CONSTRAINT` ↦ `state_constraint`. Both keep out-of-bound states out of the distinct count and don't expand them, but they differ at the boundary. TLC still checks invariants on a pruned state, counts it as generated, and doesn't treat pruning as deadlock. Veil drops the state unchecked and uncounted, and reports a deadlock where all successors are pruned (unless `termination` holds). So with a constraint, either turn deadlock checking off on both sides or, if the cfg checks deadlock, argue that no reachable state has all its successors pruned (e.g. some choice of the action that crosses the bound always stays inside). Likewise, argue that the actions crossing the bound preserve the invariants, or expect that a violation TLC finds in a just-pruned state won't appear in Veil. Guarding every action with the constraint instead checks those states but also counts them.
- `ACTION_CONSTRAINT` has no direct counterpart; an `assume` over old and new values at the end of each action comes closest. Check its boundary behavior on a tiny instance.

## When Veil misbehaves

This skill keeps no list of Veil bugs: Veil changes, and such notes go stale. When Veil rejects or warns about an encoding that should work, or fails with an error that doesn't say what is wrong:

- Reduce it to a minimal example, a small module that shows the failure and nothing else, and record the error and the Veil version. Give it to the user, and suggest they report it to the Veil maintainers.
- If the translation has to go on, work around the failure with a comment that names it, and list it among the remaining gaps.
- Try the direct form before any detour. Keep a detour only for a failure you can reproduce now, not for one that an older note describes.

`set_option veil.deferVCGeneration true`, placed before the first action, skips generating verification conditions, which `#model_check` doesn't need, so it suits a module meant for model checking. It only postpones failures in that generation to the first verification command (e.g. `#check_invariants`); build once with it off and report what it hides.
