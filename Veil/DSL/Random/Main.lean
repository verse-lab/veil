import Lean
import Lean.Parser
import Veil.Util.Meta
import Veil.Util.DSL
import Veil.Model.TransitionSystem
import Veil.DSL.Specification.SpecDef

open Lean Lean.Elab.Command Lean.Meta Lean.Elab.Term

def deriveGen (inductiveTypeStx : Term) : TermElabM Syntax := do
  let inductiveTypeTerm <- elabTerm inductiveTypeStx none
  let .some inductiveType := inductiveTypeTerm.getAppFn.constName?
    | throwError "{inductiveTypeStx} is not an inductive type"
  let env ← getEnv
  let .some inductiveTypeConst := env.find? inductiveType
    | throwError "inductive type {inductiveType} not found"
  unless inductiveTypeConst.isInductive do
    throwError "inductive type {inductiveType} is not an inductive type"
  let inductiveInfo := inductiveTypeConst.inductiveVal!
  let ctorsNum := inductiveInfo.numCtors
  -- let mut matchAlts := #[]
  let mut ctorNames := #[]
  let mut nums := #[]
  let mut sampleArgs := #[]
  for i in [0:ctorsNum] do
    nums := nums.push $ <- `(term| $(Syntax.mkNatLit i):term)
    let ctorName := inductiveInfo.ctors[i]!
    let .some (.ctorInfo ctorInfo) := env.find? ctorName | throwError "ctor {ctorName} not found"
    ctorNames := ctorNames.push $ mkIdent ctorName
    let ctorNumber := ctorInfo.numFields
    let mut sampleArg := #[]
    for _ in [0:ctorNumber] do
      sampleArg := sampleArg.push $ <- `(term| (<- Plausible.SampleableExt.interpSample _))
    sampleArgs := sampleArgs.push $ sampleArg
  `(command| def  $(mkIdent $ inductiveType ++ `gen) :
     Plausible.Gen $inductiveTypeStx := do
        match <- Plausible.Gen.chooseAny (Fin $(Syntax.mkNatLit ctorsNum):term) with
        $[| Fin.mk $nums _ => return $ctorNames $sampleArgs* ]*)

elab "#deriveGen" t:term : command => do
  let stx <- runTermElabM (fun _ => deriveGen t)
  elabCommand stx
