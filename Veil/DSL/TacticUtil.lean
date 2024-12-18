import Lean
import Lean.Parser
import Veil.Tactic
open Lean Elab

open Tactic
def run (t: TacticM Syntax): TacticM Unit := Tactic.withMainContext do
    evalTactic (<- t)

def tryGoal (t: TacticM Unit): TacticM Unit := do
  t <|> return ()

def getCtxNames (ctx : LocalContext) : TacticM (Array Name) := do
  let mut hyps := #[]
  for hyp in ctx do
    hyps := hyps.push hyp.userName
  return hyps
