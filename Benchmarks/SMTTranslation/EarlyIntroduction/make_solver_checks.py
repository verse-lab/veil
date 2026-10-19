#!/usr/bin/env python3
"""Generate matched old/early SMT outcome probes for seven Veil examples."""
from pathlib import Path
import argparse, json, re

MODELS = [
    ('Ring', 'Examples/Ivy/Ring.lean', '∃ l, leader l'),
    ('DieHard', 'Examples/Puzzles/DieHard.lean', 'big = 4'),
    ('TwoPhaseCommit', 'Examples/Ivy/TwoPhaseCommit.lean', '∃ n, decide_commit n'),
    ('RicartAgrawala', 'Examples/Ivy/RicartAgrawala.lean', '∃ n, holds n'),
    ('MultiSigAll', 'Examples/Ivy/MultiSigAll.lean', '∃ n k v d, paid n k v d'),
    ('Peterson', 'Examples/TLA/Peterson.lean', '∃ p, pc p critical ∨ pc p release'),
    ('FloodSet', 'Examples/Synchronous/FloodSet.lean', '∃ n v, decision n v'),
]

data_prefix_helper = 'open Lean Meta Elab Tactic Veil\n\nmeta section\n\npartial def introDataPrefix (goal : MVarId) : MetaM MVarId := goal.withContext do\n  let target ← instantiateMVars (← goal.getType)\n  let .forallE _ domain _ _ := target.consumeMData | return goal\n  if ← isProp domain then return goal\n  let (_, goal\') ← withOptions (fun opts => opts.setBool `tactic.hygienic false) goal.intro1\n  introDataPrefix goal\'\n\nelab "intro_data_prefix" : tactic => do\n  liftMetaTactic1 fun goal => return some (← introDataPrefix goal)\n\nend\n'

helper='''
open Lean Elab Tactic Meta Veil
elab "check_solver_outcome " label:str : tactic => withMainContext do
  let start ← IO.monoMsNow
  try
    let hs := (← getFVarIds (← Veil.getPropsInContext)).map Expr.fvar
    let original ← getMainGoal
    let mut mv := (← Meta.mkFreshExprMVar (← original.getType)).mvarId!
    mv ← mv.cleanup (← hs.foldlM (fun s h => return (← (Expr.collectFVars h).run s).snd) {}).fvarIds
    let steps := #[Smt.Preprocess.pushHintsToCtx, Smt.Preprocess.intros, Smt.Preprocess.negateGoal,
      Smt.Preprocess.normalize, Smt.Preprocess.embeddingWithConfig { embedBool := false }]
    let ⟨_, hs, normalizedGoal⟩ ← mv.withContext <| Smt.Preprocess.applySteps mv hs steps
    let cmds ← normalizedGoal.withContext do
      let (fvNames, _) ← Smt.genUniqueFVarNames
      Smt.prepareSmtQuery hs.toList fvNames
    let cmds := Smt.Translate.Command.setLogic "ALL" :: cmds
    let query := Smt.Translate.Command.cmdsAsQuery cmds
    let path := __OUTPUT_PREFIX__ ++ label.getString ++ ".smt2"
    IO.FS.writeFile path (Smt.Translate.Command.cmdsAsQuery (cmds ++ [.checkSat]))
    let prepared ← IO.monoMsNow
    let options := Smt.defaultSolverOptions ++ [("finite-model-find", "true"),
      ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")]
    let result ← Smt.solve query (some __TIMEOUT__) false options
    let status := match result with
      | .ok (.sat _) => "sat"
      | .ok (.unsat _ _) => "unsat"
      | .ok (.unknown reason) => "unknown:" ++ reason.toString
      | .error err => "error:" ++ err.toString
    IO.println s!"SOLVER_RESULT {label.getString} status={status} solver_ms={(← IO.monoMsNow)-prepared} smt_prep_ms={prepared-start} bytes={query.utf8ByteSize}"
  catch ex =>
    IO.println s!"SOLVER_FAILURE {label.getString}: {← ex.toMessageData.toString}"
    throw ex

'''
pipeline='''  veil_simp +instances only [nextSimp]
  veil_simp +instances only [↓ existsQuantifierSimpGuarded]
  veil_intros
  veil_destruct
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
  veil_simp +instances only [smtSimp]
  try dsimp +instances [Inhabited.default, FieldAbstractType, State.Label.toDomain, State.Label.toCodomain]
'''

def generate(repo, output, selected, depths, solver_timeout):
    output.mkdir(parents=True, exist_ok=True)
    models = [m for m in MODELS if m[0] in selected]
    rendered_helper = data_prefix_helper + helper.replace('__OUTPUT_PREFIX__', json.dumps(str(output) + '/'))
    rendered_helper = rendered_helper.replace('__TIMEOUT__', str(solver_timeout))
    for name, file, assertion in models:
        src = (repo / file).read_text()
        boundary = re.search(r'^\s*(?:#time\s+)?#gen_spec\b', src, re.M)
        if boundary is None:
            raise ValueError(f'no #gen_spec boundary in {file}')
        src = src[:boundary.start()] + '\nset_option veil.smt.trust true\n#gen_spec\n'
        settings = '\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 10000\n'
        src = src.replace('public import Veil\n', 'public import Veil\n' + settings + rendered_helper, 1)
        for depth in depths:
            for mode in ['old', 'early']:
                src += f'\nunsat trace [solver_{mode}_{depth}] {{\n  any {depth} actions\n  assert ({assertion})\n}} by\n'
                if mode == 'early':
                    src += '  intro_data_prefix\n'
                src += pipeline + f'  check_solver_outcome "{name}_{mode}_{depth}"\n  sorry\n'
        src += f'\nend {name}\n'
        (output / (name + '.lean')).write_text(src)
    (output / 'models.json').write_text(json.dumps(models, indent=2) + '\n')
    return models


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--models', nargs='+', choices=[m[0] for m in MODELS], default=[m[0] for m in MODELS])
    parser.add_argument('--depths', nargs='+', type=int, default=[4, 8])
    parser.add_argument('--solver-timeout', type=int, default=10)
    args = parser.parse_args()
    generate(args.repo.resolve(), args.output.resolve(), args.models, args.depths, args.solver_timeout)

if __name__ == '__main__':
    main()
