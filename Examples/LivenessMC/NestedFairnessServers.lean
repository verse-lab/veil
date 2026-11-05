module

public import Veil
public import Veil.Core.Tools.LivenessMC.LivenessMC
public meta import Veil.Core.Tools.LivenessMC.LivenessMC
public meta import Veil.Core.Tools.LivenessMC.Report
public meta import Veil.Core.Tools.LivenessMC.Benchmarking
import Lasso

/-! # Nested fairness: a fairness assumption TLC has to build a tableau for

    Three request-processing servers. Each sits idle until it accepts a request, processes it, and
    emits a reply, and from the receiving or working stage it may instead abort back to idle.

    Q: does server 0 emit infinitely often?
    - No: every server can accept-then-abort forever and never emit.

    The assumption that fixes it is that each server's whole cycle completes infinitely often,
    `□◇(recv i ∧ ◇(work i ∧ ◇emit i))`. The abort edge is what earns the nesting: `□◇recv i` alone
    is satisfied by the accept-then-abort loop and still never emits.

    Write the property as `fairness → property`. The routing is automatic and
    `explainFairness` below reports it: which conjuncts were hoisted, which stayed in the property,
    and what the hoisted ones cost.

    That formula is a fairness in the sense of [LSFZ16] but it is not literally `□◇P` for a state
    predicate `P`, so TLC's classifier files it as a residual temporal formula and builds a tableau.
    Ours applies `GF(φ ∧ ◇ψ) ≡ GF φ ∧ GF ψ` twice per conjunct first, so the whole assumption
    flattens to nine acceptance marks in a single disjunct and the tableau only ever sees `□◇emit 0`.
-/

veil module NestedServers

abbrev Server := Fin 3

relation recv : Server -> Bool
relation work : Server -> Bool
relation emit : Server -> Bool

#gen_state

after_init {
  recv S := false
  work S := false
  emit S := false
}

-- idle is all three false, so `accept` is the only move out of it
action accept (s : Server) {
  require recv s = false ∧ work s = false ∧ emit s = false
  recv s := true
}
action process (s : Server) {
  require recv s = true
  recv s := false
  work s := true
}
action send (s : Server) {
  require work s = true
  work s := false
  emit s := true
}
action finish (s : Server) {
  require emit s = true
  emit s := false
}
-- the abort edge, which is what makes `□◇recv` too weak an assumption
action abort (s : Server) {
  require recv s = true ∨ work s = true
  recv s := false
  work s := false
}

safety [oneStage] ¬(recv 0 = true ∧ work 0 = true)

-- False: every server can accept then abort forever.
temporal [server0Emits] □ ◇ ⌜ emit 0 = true ⌝

-- False too: the accept-then-abort loop satisfies it and never emits.
temporal [server0EmitsWeak]
  (□ ◇ ⌜ recv 0 = true ⌝) → □ ◇ ⌜ emit 0 = true ⌝

-- True: each server's whole cycle completes infinitely often.
temporal [server0EmitsFair]
  ( (□ ◇ (⌜ recv 0 = true ⌝ ∧ ◇ (⌜ work 0 = true ⌝ ∧ ◇ ⌜ emit 0 = true ⌝)))
  ∧ (□ ◇ (⌜ recv 1 = true ⌝ ∧ ◇ (⌜ work 1 = true ⌝ ∧ ◇ ⌜ emit 1 = true ⌝)))
  ∧ (□ ◇ (⌜ recv 2 = true ⌝ ∧ ◇ (⌜ work 2 = true ⌝ ∧ ◇ ⌜ emit 2 = true ⌝))) )
  → □ ◇ ⌜ emit 0 = true ⌝

#gen_spec

#gen_executable

/-! ## Benchmark

`checkFair` hoists every fairness conjunct that flattens, so its tableau only ever sees
`□◇emit 0` and the assumption becomes nine acceptance marks in a single disjunct.

There is no translated-assumption row because there cannot be one. Handing `server0EmitsFair` to a checker
that translates the whole implication overflows the tableau construction, which is the same wall TLC hits on
`NestedFairnessServers.tla`, where it fails to finish at three servers. The two negative controls use the
verified `checkNDFS` entry point so nothing here depends on a `sorry`. -/

open Veil.LivenessMC in
private def timeIt {α} (name : String) (f : Unit → Lasso.EmptinessResult α) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r := f ()
  let d := match r with
    | .empty k => s!"holds, explored {k}"
    | .nonEmpty stem loop => s!"fails, counterexample {stem.length}+{loop.length}"
  let t1 ← IO.monoNanosNow
  IO.println s!"  {name}: {d}  [{(t1 - t0) / 1000000}ms]"

-- What the router does with each assumption, before any checking happens.
#eval show IO Unit from do
  Veil.LivenessMC.explainFairness (server0EmitsWeak.ast Theory (State FieldConcreteType) FieldConcreteType)
  Veil.LivenessMC.explainFairness (server0EmitsFair.ast Theory (State FieldConcreteType) FieldConcreteType)

#eval show IO Unit from do
  IO.println "NestedServers, 3 servers, 64 states"
  timeIt "no assumption          " fun _ =>
    Veil.LivenessMC.checkNDFS (enumerableTransitionSystem {})
      (server0Emits.ast Theory (State FieldConcreteType) FieldConcreteType)
      (by native_decide) (by native_decide)
  timeIt "weak assumption        " fun _ =>
    Veil.LivenessMC.checkNDFS (enumerableTransitionSystem {})
      (server0EmitsWeak.ast Theory (State FieldConcreteType) FieldConcreteType)
      (by native_decide) (by native_decide)
  timeIt "nested assumption, hoisted" fun _ =>
    Veil.LivenessMC.checkFair (enumerableTransitionSystem {})
      (server0EmitsFair.ast Theory (State FieldConcreteType) FieldConcreteType)

/-! ## Veil callbacks per product state

`1.0x` means a callback is entered once per product state, which is what Lasso's fused `expand` buys, anything above
means once per edge. See `EdgeLabels.md` §9. Every conjunct of `server0EmitsFair` hoists, so the kept property is `⊤` and
the search settles without walking the product, which is why the ratio has no product state to divide by. -/
#eval show IO Unit from do
  Veil.LivenessMC.resetVeilTimers
  let t0 ← IO.monoNanosNow
  let r := Veil.LivenessMC.checkFairTimed (enumerableTransitionSystem {})
    (server0EmitsFair.ast Theory (State FieldConcreteType) FieldConcreteType)
  let (verdict, states) := match r with
    | .empty k => (s!"holds, {k} product states", k)
    | .nonEmpty stem loop => (s!"fails, cex {stem.length}+{loop.length}", 0)
  let t1 ← IO.monoNanosNow
  let v ← Veil.LivenessMC.readVeilTimers
  let per (c : Nat) : String :=
    if states == 0 then "-" else s!"{c * 10 / states / 10}.{c * 10 / states % 10}x"
  IO.println s!"nested assumption via the product latch: {verdict}, {(t1 - t0) / 1000000}ms"
  IO.println s!"  successors {v.succCalls} calls ({per v.succCalls} per product state)"
  IO.println s!"  labeling   {v.labelCalls} calls ({per v.labelCalls} per product state)"

end NestedServers
