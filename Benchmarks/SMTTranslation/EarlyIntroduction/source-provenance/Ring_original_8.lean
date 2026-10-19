module
public import Veil
public meta import Lean.Util.NumObjs

/-!
Stage measurements for issue #123, using the Ring example at depth 32.
Run from the repository root with:
  lake env lean Benchmarks/SMTTranslation/Pipeline.lean

This is a measurement scaffold, not a verified theorem: the final `sorry`
closes the generated trace proposition. The probe normalizes a duplicate
goal and writes SMT-LIB without running a solver. The trace command's
polarity therefore does not report a SAT/UNSAT result.

The experimental change is to introduce the outer trace binders, destruct
the State/Theory records, and simplify their dispatcher types before
nextSimp and the guarded quantifier pass. It leaves the trace conjunction
on the target. This avoids triggering the expensive existential pass solely
because of the outer records. Nested higher-order witnesses still use the
existing guarded hoisting pass.

`target_nodes` counts distinct expression objects in the target only; it
excludes context, proof terms, and SMT output. Timings are wall-clock ms.
The SMT phases match the default trusted Veil path (`embedBool := false`).
The retained probe uses ordinary Veil heartbeat/recursion limits and the
default simp step cap. Both depths 32 and 128 were tested with those limits.
-/
open Lean Elab Tactic Meta Veil
elab "bench_stage " label:str t:tactic : tactic => do
  let start ← IO.monoMsNow
  try
    evalTactic t
    let elapsed := (← IO.monoMsNow) - start
    let goals ← getGoals
    let mut nodes := 0
    for g in goals do
      nodes := nodes + (← (← g.getType).numObjs)
    IO.println s!"STAGE {label.getString} ms={elapsed} goals={goals.length} target_nodes={nodes}"
  catch ex =>
    IO.println s!"FAILED {label.getString} ms={(← IO.monoMsNow) - start}: {← ex.toMessageData.toString}"
    throw ex

/-- Exercise lean-smt preprocessing and translation on a fresh duplicate goal. -/
elab "bench_smt_pipeline " path:str : tactic => withMainContext do
  let hs := (← getFVarIds (← Veil.getPropsInContext)).map Expr.fvar
  let goal ← getMainGoal
  let mut mv := (← Meta.mkFreshExprMVar (← goal.getType)).mvarId!
  mv ← mv.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
  let mut hs := hs
  let steps : Array (String × (MVarId → Array Expr → MetaM Smt.Preprocess.Result)) := #[
    ("pushHints", Smt.Preprocess.pushHintsToCtx),
    ("smt-intros", Smt.Preprocess.intros),
    ("negateGoal", Smt.Preprocess.negateGoal),
    ("normalize", Smt.Preprocess.normalize),
    ("embedding", Smt.Preprocess.embeddingWithConfig { embedBool := false })]
  for (name, step) in steps do
    let start ← IO.monoMsNow
    let r ← mv.withContext <| step mv hs
    mv := r.mv
    hs := r.hs
    IO.println s!"SMT_STAGE {name} ms={(← IO.monoMsNow)-start} hypotheses={hs.size}"
  let start ← IO.monoMsNow
  let cmds ← mv.withContext do
    let (fvNames, _) ← Smt.genUniqueFVarNames
    Smt.prepareSmtQuery hs.toList fvNames
  IO.println s!"SMT_STAGE translate ms={(← IO.monoMsNow)-start} commands={cmds.length}"
  let start ← IO.monoMsNow
  let query := Smt.Translate.Command.cmdsAsQuery (.setLogic "ALL" :: cmds ++ [.checkSat])
  let outputPath := System.FilePath.mk path.getString
  if let some parent := outputPath.parent then IO.FS.createDirAll parent
  IO.FS.writeFile outputPath query
  IO.println s!"SMT_STAGE serialize ms={(← IO.monoMsNow)-start} bytes={query.utf8ByteSize}"

veil module Ring


type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node → Bool
relation pending : node → node → Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

ghost relation isNext (n : node) (next : node) :=
  ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)

action send (n next : node) {
  require isNext n next
  pending n next := true
}

action recv (sender n next : node) {
  require isNext n next
  require pending sender n
  pending sender n := false
  if (sender = n) then
    leader n := true
  else
    if (le n sender) then
      pending sender next := true
}

safety [single_leader] leader N ∧ leader M → N = M
invariant [leader_greatest] leader L → le N L
invariant [self_msg_greatest] pending L L → le N L
invariant [drop_smaller] pending S D ∧ btw S N D → le N S


#gen_spec
-- Keep ordinary Veil heartbeat/recursion limits and the default simp step cap.
sat trace [pipeline_probe] {
 any 8 actions
 assert (∃ l, leader l)
} by
  bench_stage "nextSimp" (veil_simp +instances only [nextSimp])
  bench_stage "hoist" (veil_simp +instances only [↓ existsQuantifierSimpGuarded])
  bench_stage "intros" veil_intros
  bench_stage "destruct" veil_destruct
  bench_stage "dsimp1" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  bench_stage "smtSimp" (veil_simp +instances only [smtSimp])
  bench_stage "dsimp2" (try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain])
  bench_smt_pipeline "/tmp/veil-issue123-equivalence/original8.smt2"
  sorry
end Ring
