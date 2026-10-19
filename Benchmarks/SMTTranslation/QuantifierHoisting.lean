import Veil.Frontend.DSL.Infra.Quantifiers
import Lean.Util.NumObjs

/-!
Isolate the existential-hoisting cost discussed in issue #123.

Run with:
  lake env lean Benchmarks/SMTTranslation/QuantifierHoisting.lean

The input is a conjunction of `depth` transitions. Each transition is a
disjunction of `branches` alternatives, each with `witnesses` existentially
quantified functions. An opaque predicate prevents simplification from deleting
the witnesses. The matrix only passes first-order Boolean values (`f 0`) to
that predicate; after witness extraction, its function symbols have first-order
types. Input and normalized formula sizes grow linearly in depth.

`global` hoists the entire formula. `local` independently normalizes each
transition and sums the work. The latter measures the normalization component
of a possible pipeline that first splits the trace conjunction into hypotheses;
it excludes the proof scaffolding required to split and reassemble those
hypotheses. It is not an end-to-end SMT benchmark.

The simp context is created once per measurement, outside the timer, and reused
across transitions in local mode. The guard and normalization are timed
separately. `steps` is Lean simp's step
counter; `hb` counts raw allocation heartbeats, not the scaled maxHeartbeats
option. `proofDistinct` counts structurally distinct Expr subterms (a maximally
shared DAG), `proofObjects` counts actual allocated Expr objects, and `proofTree`
counts occurrences with sharing expanded. Size measurement happens after the
normalization timer stops. No proof is admitted; normalization uses the existing
proof-producing simp rules. These measurements exclude kernel checking.

The final argument is maxSteps. The large budget in the main series is for
timing only: it must not be mistaken for a proposed fix. The stock 100,000-step
budget is exercised separately at the end. Max heartbeats and recursion depth
are raised to distinguish the algorithmic costs from those resource limits.
-/

open Lean Meta Elab Command

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace QuantifierHoistingBenchmark

opaque atom : Nat → Bool → Prop

private def joinNonempty (op : Name) (es : Array Expr) : Expr := Id.run do
  let mut out := es.back!
  for e in es.pop.toList.reverse do
    out := mkApp2 (mkConst op) e out
  return out

private def mkBranch (id witnesses : Nat) : Expr := Id.run do
  let ty := mkForall `x .default (mkConst ``Nat) (mkConst ``Bool)
  let atoms := (List.range witnesses).toArray.map fun i =>
    mkApp2 (mkConst ``atom) (mkNatLit (id * 1000 + i))
      (mkApp (mkBVar (witnesses - i - 1)) (mkNatLit 0))
  let mut out := joinNonempty ``And atoms
  for i in [:witnesses] do
    out := mkApp2 (mkConst ``Exists [1]) ty (mkLambda (.mkSimple s!"f{i}") .default ty out)
  return out

private def mkTransition (id branches witnesses : Nat) : Expr :=
  joinNonempty ``Or <| (List.range branches).toArray.map fun i =>
    mkBranch (id * 1000 + i) witnesses

private partial def distinctNodes (e : Expr) : StateM ExprSet Nat := do
  if (← get).contains e then return 0
  modify (·.insert e)
  e.foldlM (fun n c => return n + (← distinctNodes c)) 1

private partial def peelExists (e : Expr) : Nat × Expr :=
  if e.isAppOfArity ``Exists 2 then
    let (n, matrix) := peelExists e.appArg!.bindingBody!
    (n + 1, matrix)
  else (0, e)

elab "#hoist_bench " depth:num branches:num witnesses:num mode:str budget:num : command => do
  liftTermElabM do
    let d := depth.getNat
    let b := branches.getNat
    let w := witnesses.getNat
    let locally ← match mode.getString with
      | "global" => pure false
      | "local" => pure true
      | _ => throwError "expected global or local"
    unless d > 0 && b > 0 && w > 0 do
      throwError "depth, branches, and witnesses must be positive"
    let terms := (List.range d).toArray.map fun i => mkTransition i b w
    let whole := joinNonempty ``And terms
    let maxSteps := budget.getNat
    let ctx ← Veil.Simp.mkVeilSimpCtx #[`existsQuantifierSimp] { maxSteps }
    let some ext ← Lean.Meta.Simp.getSimprocExtension? `existsQuantifierSimp
      | throwError "missing existsQuantifierSimp simprocs"
    let procs := #[← ext.getSimprocs]
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoMsNow
    let guard ← Veil.hasHOQuantification whole
    let t1 ← IO.monoMsNow
    let h1 ← IO.getNumHeartbeats
    try
      let mut outputs := #[]
      let mut steps := 0
      for e in (if locally then terms else #[whole]) do
        let (r, s) ← Veil.withBackwardsCompatibility <| Lean.Meta.simpCore e ctx procs
        outputs := outputs.push r
        steps := steps + s.numSteps
      let t2 ← IO.monoMsNow
      let h2 ← IO.getNumHeartbeats
      let mut outNodes := 0
      let mut proofDistinct := 0
      let mut proofObjects := 0
      let mut proofTree := 0
      let mut prefixWitnesses := 0
      for r in outputs do
        outNodes := outNodes + r.expr.sizeWithoutSharing
        let (n, matrix) := peelExists r.expr
        prefixWitnesses := prefixWitnesses + n
        if (matrix.find? (fun e => e.isAppOfArity ``Exists 2)).isSome then
          throwError "normalization left an existential inside the matrix"
        if let some p := r.proof? then
          proofDistinct := proofDistinct + Id.run ((distinctNodes p).run' {})
          proofObjects := proofObjects + (← p.numObjs)
          proofTree := proofTree + p.sizeWithoutSharing
      unless prefixWitnesses == d * b * w do
        throwError "incorrect witness count: {prefixWitnesses}, expected {d * b * w}"
      IO.println s!"HOIST mode={mode.getString} d={d} b={b} w={w} budget={maxSteps} in={whole.sizeWithoutSharing} out={outNodes} witnesses={prefixWitnesses} proofDistinct={proofDistinct} proofObjects={proofObjects} proofTree={proofTree} guard={guard} guardMs={t1-t0} simpMs={t2-t1} guardHB={h1-h0} simpHB={h2-h1} steps={steps}"
    catch ex =>
      let message ← ex.toMessageData.toString
      IO.println s!"HOIST mode={mode.getString} d={d} b={b} w={w} budget={maxSteps} failedMs={(← IO.monoMsNow)-t1} error={message}"
      unless message == "`simp` failed: maximum number of steps exceeded" do
        throw ex
    (← IO.getStdout).flush

#hoist_bench 1 2 1 "global" 100000000
#hoist_bench 2 2 1 "global" 100000000
#hoist_bench 4 2 1 "global" 100000000
#hoist_bench 8 2 1 "global" 100000000
#hoist_bench 16 2 1 "global" 100000000
#hoist_bench 32 2 1 "global" 100000000
#hoist_bench 1 2 1 "local" 100000000
#hoist_bench 2 2 1 "local" 100000000
#hoist_bench 4 2 1 "local" 100000000
#hoist_bench 8 2 1 "local" 100000000
#hoist_bench 16 2 1 "local" 100000000
#hoist_bench 32 2 1 "local" 100000000

-- Extra branch/witness pressure at a fixed trace depth.
#hoist_bench 8 4 2 "global" 100000000
#hoist_bench 8 4 2 "local" 100000000

-- Check the stock simplifier step budget independently of timing-only runs.
#hoist_bench 16 2 1 "global" 100000
#hoist_bench 22 2 1 "global" 100000
#hoist_bench 23 2 1 "global" 100000
#hoist_bench 32 2 1 "global" 100000

end QuantifierHoistingBenchmark
