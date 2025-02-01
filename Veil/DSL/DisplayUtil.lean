import Lean
import Veil.DSL.Util
import Veil.SMT.Main

open Lean Elab Meta Tactic TryThis

def displaySuggestion (stx : Syntax) (theorems : Array (TSyntax `command)) (preMsg : Option String := none) := do
    Command.liftTermElabM do
    let cmd ← constructCommands theorems
    let suggestion : Suggestion := {
      suggestion := cmd
      preInfo? := preMsg
      toCodeActionTitle? := .some (fun _ => "Replace with explicit proofs.")
    }
    addSuggestion stx suggestion (header := "")

def emoji (res : SmtResult) : String :=
  match res with
  | .Unsat => "✅"
  | .Sat _ => "❌"
  | .Unknown _ => s!"❓"
  | .Failure reason => s!"💥 {reason}"

def getBaseNameForDisplay (n : Name) : Name := n.updatePrefix Name.anonymous

structure TheoremIdentifier where
  invName : Name
  /-- If it's `none`, it's the initial action. -/
  actName : Option Name
  theoremName : Name
deriving Inhabited, BEq

def getInitCheckResultMessages' (res: List (Name × SmtResult)) : (Array String) := Id.run do
  let mut msgs := #[]
  if !res.isEmpty then
    msgs := msgs.push "Initialization must establish the invariant:"
    for (invName, r) in res do
      msgs := msgs.push s!"  {getBaseNameForDisplay invName} ... {emoji r}"
  pure msgs

def getInitCheckResultMessages (res : List (TheoremIdentifier × SmtResult)) := getInitCheckResultMessages' (res.map (fun (id, r) => (id.invName, r)))

/-- `(invName, actName, result)` -/
def getActCheckResultMessages' (res: List (Name × Name × SmtResult)) : (Array String) := Id.run do
  let mut msgs := #[]
  if !res.isEmpty then
    msgs := msgs.push "The following set of actions must preserve the invariant:"
    for (actName, invResults) in group res do
      msgs := msgs.push s!"  {actName}"
      for (invName, r) in invResults do
        msgs := msgs.push s!"    {getBaseNameForDisplay invName} ... {emoji r}"
  pure msgs
where group {T : Type} (xs : List (Name × T)) : List (Name × List T) :=
  xs.foldl (fun acc (key, val) =>
    match acc.find? (fun (k, _) => k = key) with
    | some (k, vs) =>
          acc.filter (fun (k', _) => k' ≠ key) ++ [(k, vs ++ [val])]
    | none =>
      acc ++ [(key, [val])]) []

def getActCheckResultMessages (res : List (TheoremIdentifier × SmtResult)) := getActCheckResultMessages' (res.map (fun (id, r) => (id.actName.get!, id.invName, r)))
