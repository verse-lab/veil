module

public import Veil.DSL
public import Veil.Core.Tools.Synthesizer.Soundness
public meta import Veil.Core.Tools.Synthesizer.Command

/-!
# Invariant synthesis

`#updr`, run after `#gen_spec` in a Veil module, finds universal `invariant`
clauses that make the module's `safety` properties and declared `invariant`s inductive, finds
an execution that violates them, or reports that no universal inductive invariant exists. With `certify`, an invariant or an
execution is checked in the background as `ic3_safe` or `ic3_unsafe`; `#gen_theorems` waits and
imports the certificate. The search is UPDR, the
first-order form of IC3 [Karbyshev et al.]. See `docs/Synthesizer-Guide.md` for usage.

The command is part of `import Veil`.

## Structure

* `Clause`, `Structure`: universal clauses, finite structures and diagrams.
* `Linear`: linear relations between integer individuals, as candidate clauses.
* `Render`: clauses as Veil terms and as text.
* `Vocabulary`, `Model`: the symbols of a module, and solver models read as structures.
* `Query`, `TrNorm`, `Solver`: the solver queries and Veil's pipeline that discharges them.
* `Search`, `Generalize`, `Controller`: the UPDR loop.
* `Soundness`: the facts about transition systems the certificates apply.
* `Tactic`, `Certificate`, `Counterexample`: the certificates.
* `Command`: the command.

## References

* A. Karbyshev, N. Bjørner, S. Itzhaky, N. Rinetzky, S. Shoham, *Property-Directed Inference of
  Universal Invariants or Proving Their Absence*, Journal of the ACM 64(1), 2017.
-/
