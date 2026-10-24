# Veil Invariant Synthesizer Guide

`#synthesize_invariants` searches for `invariant` clauses that make a module's
`safety` properties inductive. It reports an inductive invariant, an execution
that violates the properties, or that no universal inductive invariant exists.
With `certify`, an invariant or a violation becomes a theorem checked by the
Lean kernel. Run `#gen_theorems` to add its declarations to the current module.

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

#synthesize_invariants certify
#gen_theorems

#check ic3_safe
end LockServer
```

The command prints the strengthening as lines to paste into the module, and
`certify` checks the theorem `LockServer.ic3_safe` in the background.
`#gen_theorems` waits for certification and imports it, alongside any results from
`#check_invariants`:

```
Inductive invariant found at frame 1 with 1 strengthening clause(s) (…):
invariant [ic3_0] ∀ (x0 : client), ¬ holds x0 ∨ ¬ lock_free
Certified: theorem LockServer.ic3_safe (strengthening LockServer.ic3_inv); axioms: #[propext, Classical.choice, Quot.sound]; kernel-checked, standard axioms only
```

### Live progress

In the Lean editor, put the cursor on `#synthesize_invariants` to see its progress
panel in the infoview. It shows the current activity, elapsed time, search queries
completed and the query budget, time spent in queries, clauses per frame, and
candidate/admission counts. During `certify`, it shows the current proof obligation
and the number completed. The final display distinguishes an uncertified search
result from a certificate and reports any additional axioms used by the certificate.

The query budget is a work limit, not a percentage of completion: the search does
not know how many queries will be needed. Query time includes elaboration,
preprocessing, solving, and decoding; internal solver retries are included in the
same search query. Certification has its own obligation count.

Search and certification run in a dedicated background task. The launching command
returns immediately, so the panel updates during long queries and later commands
can elaborate. Closing and reopening the panel does not stop synthesis or lose
progress. Editing the command cancels the old run. `#gen_theorems` waits for the
module's pending certificates and imports their declarations before subsequent
commands use them; declarations written between the two commands are preserved.

Use `set_option veil.synthesizer.widget false` to disable the panel. Command-line
builds do not create a widget. For progress outside the editor, use `verbose` or
`(log := "run.jsonl")` and watch the log with `tail -F run.jsonl`.

`#guard_msgs` deliberately waits for background diagnostics, so a panel inside it
appears after completion. Use a direct `#synthesize_invariants` command for live
updates.

### Options

Options may appear in any order, each at most once:
`#synthesize_invariants (fuel := 500) (log := "run.jsonl") verbose certify`.

| option | meaning | default |
|---|---|---|
| `(fuel := n)` | Maximum number of solver calls. | 5000 |
| `(invariants := true)` | Include the module's declared `invariant`s in the property. | `false` |
| `(generalizer := g)` | `linear` first tries linear relations between integer individuals, then `updr`; `updr` uses unsat cores and literal deletion only. They agree on a module without integer state. | `linear` |
| `(cores := false)` | Generalize by deleting literals from the full negated diagram, as the paper does, instead of starting from the solver's unsat cores. | `true` |
| `(log := "path.jsonl")` | Append one JSON object per event (each candidate clause and its verdict, each clause admitted, each frame cleared, the outcome) to this file. | no log |
| `(expect := v)` | The expected outcome: `invariant`, `unsafe`, `no_universal_invariant` or `unknown`. It is reported as information, any other outcome as an error. For tests. | none |
| `verbose` | Report each step of the search. | off |
| `certify` | Check a certificate in the background; `#gen_theorems` imports it. | off |

| Lean option | meaning | default |
|---|---|---|
| `veil.synthesizer.trust` | Let the search take the solver's `unsat` answers on faith instead of reconstructing proofs. Certificates always reconstruct. | `false` |
| `veil.synthesizer.normalizeTr` | Write the queries with the transition relation normalized once per module (`Mod.ic3_trNorm`, equal to `tr` by the kernel-checked `Mod.ic3_tr_eq_norm`). | `true` |
| `veil.synthesizer.timings` | Report the wall time of the search and of the certificate. | `false` |
| `veil.synthesizer.widget` | Show live progress in the Lean editor's infoview. | `true` |
| `veil.smt.timeout` | The solver timeout. A query the search cannot do without is asked again with twice the timeout before the search stops. | 60 s |

## Reading the Result

| outcome | `expect` value | what is printed | with `certify` |
|---|---|---|---|
| Inductive invariant | `invariant` | The strengthening as `invariant [ic3_k] …` lines, none when the property is inductive on its own. | `Mod.ic3_safe : ∀ th st, reachable th st → ic3_prop th st`. |
| Violation | `unsafe` | An execution from an initial state to a state violating the property, and a `sat trace` block that re-checks it. An error unless expected. | `Mod.ic3_unsafe`: at the model's sort sizes and typeclass instances, not every reachable state satisfies `ic3_prop`. |
| No universal inductive invariant | `no_universal_invariant` | An abstract counterexample: finite structures, the first contained in an initial state, each next contained in a successor of a state containing the previous, and a successor of the last violating the property. | Nothing: the verdict is not a theorem. |
| Stopped | `unknown` | Why the search stopped and the clauses per frame. | Nothing. |

The search stops when it runs out of fuel, passes 40 frames, gets no answer to
a query it cannot do without (even with twice the timeout), or cannot pose a
query or decode a model. A
module holds one certificate, since the theorem names are fixed.

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

## What `certify` Guarantees

Without `certify`, lean-smt reconstructs each `unsat` answer as a proof term,
but the search does not have the kernel check it; an answer lean-smt cannot
replay is taken on the solver's word, and the result says so. `certify`
builds the theorem from fresh solver answers. `#gen_theorems` imports its checked
definitions and proofs; it does not rerun synthesis or certification:

- **Invariant.** For each conjunct of `ic3_inv` (the property and the
  strengthening), initiation and consecution from `ic3_inv` are asked again,
  and lean-smt's proofs become theorems once the kernel accepts them.
  `ic3_safe` applies `RelationalTransitionSystem.invariant_of_inductive` and
  `Invariant.mono` (`Veil/Core/Tools/Synthesizer/Soundness.lean`).
- **Violation.** The theory, the states and the typeclass instances become
  definitions over `Fin n` and the enum types. The assumptions, the initial
  state, each step and the violation are proved by evaluation (`decide`, or
  `simp` after splitting enum variables into constructors), and `ic3_unsafe`
  applies `RelationalTransitionSystem.not_invariant_of_reachable`. Nothing
  rests on the solver. The concrete instance definitions are imported, but their
  instance registrations stay local to certification and do not affect later
  typeclass inference.
- `#print axioms` lists `propext`, `Classical.choice` and `Quot.sound`. A
  solver step that lean-smt cannot replay, or whose replay the kernel rejects,
  is taken on the solver's word as `ic3_init_i_trusted` or
  `ic3_cons_i_trusted`, with a warning; the certificate then depends on
  `sorryAx`, and the command reports it.
- A bug in the search can make a certificate fail. It cannot make a false
  theorem.

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
- **"No universal invariant" is not a theorem.** It means that no
  conjunction of universal clauses over the module's vocabulary is an
  inductive invariant implying the property, not that the property fails. It
  rests on the search, the solver's answers, and Proposition 5.6 and its
  extension, which are not formalized here.
- **No termination guarantee.** The search is bounded by fuel, 40 frames and
  the solver timeout.
- **Counterexample certificates evaluate.** A step that evaluation cannot
  prove leaves the violation reported without a theorem.
- **Results depend on solver models.** The clauses and call counts can vary
  between runs.
