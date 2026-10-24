# Veil Invariant Synthesizer Guide

`#synthesize_invariants` searches for `invariant` clauses that make a module's
`safety` properties inductive. It reports an inductive invariant, an execution
that violates the properties, or that no universal inductive invariant exists.

## Running the Synthesizer

The command is not part of `import Veil`. Import
`Veil.Core.Tools.Synthesizer` and run the command after `#gen_spec`:

```lean
module

public import Veil
public import Veil.Core.Tools.Synthesizer

veil module LockServer
-- the lock server of `VeilTest/Synthesizer/LockServer.lean`
...
safety [mutex] holds C ∧ holds D → C = D

#gen_spec

#synthesize_invariants

end LockServer
```

The command prints the strengthening as lines to paste into the module:

```
Inductive invariant found at frame 1 with 1 strengthening clause(s) (…):
invariant [ic3_0] ∀ (x0 : client), ¬ holds x0 ∨ ¬ lock_free
```

### Options

Options may appear in any order, each at most once:
`#synthesize_invariants (fuel := 500) (log := "run.jsonl") verbose`.

| option | meaning | default |
|---|---|---|
| `(fuel := n)` | Maximum number of solver calls. | 5000 |
| `(invariants := true)` | Include the module's declared `invariant`s in the property. | `false` |
| `(generalizer := g)` | `linear` first tries linear relations between integer individuals, then `updr`; `updr` uses unsat cores and literal deletion only. They agree on a module without integer state. | `linear` |
| `(cores := false)` | Generalize by deleting literals from the full negated diagram, as the paper does, instead of starting from the solver's unsat cores. | `true` |
| `(log := "path.jsonl")` | Append one JSON object per event (each candidate clause and its verdict, each clause admitted, each frame cleared, the outcome) to this file. | no log |
| `(expect := v)` | The expected outcome: `invariant`, `unsafe`, `no_universal_invariant` or `unknown`. It is reported as information, any other outcome as an error. For tests. | none |
| `verbose` | Report each step of the search. | off |

| Lean option | meaning | default |
|---|---|---|
| `veil.synthesizer.trust` | Let the search take the solver's `unsat` answers on faith instead of reconstructing proofs. | `false` |
| `veil.synthesizer.normalizeTr` | Write the queries with the transition relation normalized once per module (`Mod.ic3_trNorm`, equal to `tr` by the kernel-checked `Mod.ic3_tr_eq_norm`). | `true` |
| `veil.synthesizer.timings` | Report the wall time of the search. | `false` |
| `veil.smt.timeout` | The solver timeout. A query the search cannot do without is asked again with twice the timeout before the search stops. | 60 s |

## Reading the Result

| outcome | `expect` value | what is printed |
|---|---|---|
| Inductive invariant | `invariant` | The strengthening as `invariant [ic3_k] …` lines, none when the property is inductive on its own. |
| Violation | `unsafe` | An execution from an initial state to a state violating the property, and a `sat trace` block that re-checks it. An error unless expected. |
| No universal inductive invariant | `no_universal_invariant` | An abstract counterexample: finite structures, the first contained in an initial state, each next contained in a successor of a state containing the previous, and a successor of the last violating the property. |
| Stopped | `unknown` | Why the search stopped and the clauses per frame. |

The search stops when it runs out of fuel, passes 40 frames, gets no answer to
a query it cannot do without (even with twice the timeout), or cannot pose a
query or decode a model.

## How the Search Works

The search is UPDR, also called PDR∀: the first-order form of IC3/PDR from
A. Karbyshev, N. Bjørner, S. Itzhaky, N. Rinetzky and S. Shoham,
"Property-Directed Inference of Universal Invariants or Proving Their
Absence", *Journal of the ACM* 64(1), 2017.

- **Frames.** `F₀` is the initial states. `F₁ … F_N` are sets of universal
  clauses `∀ x̄, l₁ ∨ … ∨ lₙ` over the module's vocabulary, each together with
  the property `P`; a clause added to `F_j` is added to `F₁ … F_j`.
- **Blocking.** A state of `F_N` with a successor that violates `P` is read
  from the solver's model as a finite structure `σ`. Its diagram `Diag(σ)` is
  the existential conjunction of its facts. To exclude `σ` from `F_j`, the
  search asks for a state of `F_{j-1}` with a successor satisfying `Diag(σ)`;
  such a predecessor is excluded from `F_{j-1}` first.
- **Generalization.** Without a predecessor, a subclause `c` of `¬ Diag(σ)` is
  added. `c` must hold initially and in every successor of `F_{j-1}`. The
  candidates are tried in order: linear templates over integer individuals
  (`x + y = z`, `x ≤ y + c`, …); the literals in the unsat cores of the two
  blocking queries, then deletion of groups of literals; otherwise deletion of
  one literal at a time, cheapest first. A candidate false in a known
  reachable state is rejected without a solver call.
- **Propagation.** When `F_N` has no such state, `F_{N+1}` is opened and each
  clause of `F_i` that `F_i ∧ tr` preserves is pushed into `F_{i+1}`. When all
  of `F_i` moves, `F_i = F_{i+1}` is an inductive invariant.
- **Reaching the initial states.** When a chain of predecessors reaches `F₀`,
  one bounded query asks whether an execution of `N + 1` steps from an initial
  state violates `P`; if one does, it is the counterexample. If none does, or
  when a diagram already meets an initial state, the chain is an abstract
  counterexample, and no universal inductive invariant over the vocabulary
  implies `P` (Proposition 5.6 of the paper).

Every query goes through Veil's own tactic pipeline and cvc5, as
`#check_invariants` and `sat trace` do. Departures from the paper:

- The vocabulary has function symbols, enum sorts, typeclass symbols, and
  linear constraints over `Int`/`Nat` values. Proposition 5.6 is stated for
  constants and relations; the verdict is given for function symbols and enum
  sorts on an extension of its argument (a universal sentence passes to a
  substructure closed under the functions, and an enum carrier is fixed), and
  the message says so. With integer state it is not given, and the search
  reports that it stopped.
- The linear templates are not in the paper, nor is the shortcut that blocks
  `σ` at `F_j` with a clause of `F_{j-1}` that `σ` violates and that holds in
  every successor of `F_{j-1}`.

## Semantics

Every result is about Veil's `relationalTransitionSystem`: its initial states
run `after_init` from the default state, its transitions are the actions under
the module's `assumption`s, and `trusted invariant`s are neither assumed nor
checked. `#check_invariants` assumes trusted invariants and proves initiation
from an arbitrary pre-state, so it can reject a clause found here that relies
on a field `after_init` leaves unassigned; the command warns about such fields.

## Existential Invariants

The search finds universal clauses only. With `(invariants := true)` the
declared invariants, existentials included, are part of the property. A ghost
function that names a witness (`quorumOf : node → quorum`, maintained by the
action that elects the leader) turns an existential fact into a universal
clause over that function.

## Limitations

- **A fragment of Veil.** The vocabulary has `type` and `enum` sorts, and
  individuals, relations and functions whose arguments are sorts and whose
  values are `Bool`, a sort, `Int` or `Nat`. Typeclass instances contribute
  the relations, constants, functions and axioms of their class. The command
  refuses at startup, naming the component: an `Int`/`Nat` argument; any
  other argument or value type (`Fin n`, sets, queues, structures);
  child modules; module parameters; a class that is not a structure, extends
  another class, or has a relation or function field over other types; and
  names of the form `x0`, `x1`, ….
- **Universal clauses only.** A property whose invariant needs an
  existential, or arithmetic over a quantified index, has none in this form.
- **The results are not kernel-checked.** lean-smt reconstructs each `unsat`
  answer as a proof term, but the search does not have the kernel check it; an
  answer lean-smt cannot replay is taken on the solver's word, and the result
  says so. Paste the clauses into the module and run `#check_invariants`, or
  run the printed `sat trace` block.
- **"No universal invariant" is not a theorem.** It means that no
  conjunction of universal clauses over the module's vocabulary is an
  inductive invariant implying the property, not that the property fails. It
  rests on the search, the solver's answers, and Proposition 5.6 and its
  extension, which are not formalized here.
- **No termination guarantee.** The search is bounded by fuel, 40 frames and
  the solver timeout.
- **Results depend on solver models.** The clauses and call counts can vary
  between runs.
