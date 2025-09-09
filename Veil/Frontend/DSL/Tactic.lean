import Lean
import Veil.Frontend.DSL.Infra.State

open Lean Elab Tactic Meta Simp Tactic.TryThis

namespace Veil

instance : BEq LocalDecl := ⟨fun a b => a.userName == b.userName⟩

syntax (name := veil_destruct) "veil_destruct" (colGt ident)* : tactic

mutual

/-- Destruct a structure into its fields. -/
partial def elabVeilDestructSpecificHyp (ids : Array (TSyntax `ident)) : TacticM Unit := withMainContext do
  if ids.size == 0 then
    elabVeilDestructAllHyps (recursive := true)
  else for id in ids do
    let lctx ← getLCtx
    let name := (getNameOfIdent' id)
    let .some ld := lctx.findFromUserName? name | throwError "veil_destruct: {id} is not in the local context"
    let .some sn := ld.type.getAppFn.constName? | throwError "veil_destruct: {id} is not a constant"
    let .some _sinfo := getStructureInfo? (← getEnv) sn | throwError "veil_destruct: {id} ({sn} is not a structure)"
    let newFieldNames := _sinfo.fieldNames.map (mkIdent $ Name.append name ·)
    let s ← `(rcasesPat| ⟨ $[$newFieldNames],* ⟩)
    evalTactic $ ← `(tactic| unhygienic rcases $(mkIdent ld.userName):ident with $s)
    -- TODO: try to give better names to the new hypotheses if they are named clauses

/-- Destruct all structures in the context into their respective
fields, (potentially) recursively. Also destructs all existentials. -/
partial def elabVeilDestructAllHyps (recursive : Bool := false) (ignoreHyps : Array LocalDecl := #[]) : TacticM Unit := withMainContext do
  let mut ignoreHyps := ignoreHyps
  let hypsToVisit : (Array LocalDecl → TacticM (Array LocalDecl)) := (fun ignoreHyps => withMainContext do
    return (← getLCtx).decls.filter Option.isSome
    |> PersistentArray.map Option.get!
    |> PersistentArray.toArray
    |> Array.filter (fun hyp => !ignoreHyps.contains hyp))
  for hyp in (← hypsToVisit ignoreHyps) do
    ignoreHyps := ignoreHyps.push hyp
    if hyp.isImplementationDetail then
      continue
    let isStructure ← match hyp.type.getAppFn.constName? with
    | .none => pure false
    | .some sn => pure (isStructure (← getEnv) sn)
    let name := mkIdent hyp.userName
    if isStructure then
      let sn := hyp.type.getAppFn.constName!
      if !hypsToIgnore.contains sn then
        let dtac ← `(tactic| veil_destruct $name:ident)
        evalTactic dtac
    else
      let hypType ← Meta.whnf hyp.type
      if hypType.isAppOf ``Exists then
        let lctx ← getLCtx
        -- we want the new hypotheses to have fresh names so they're
        -- not included in the ignore list, hence we don't reuse `$name`
        let x := mkIdent $ lctx.getUnusedName (← existsBinderName hyp.type)
        let name' := mkIdent $ lctx.getUnusedName name.getId
        evalTactic $ ← `(tactic| rcases $name:ident with ⟨$x, $name'⟩)
  -- Recursively call ourselves until the context stops changing
  if recursive && (← hypsToVisit ignoreHyps).size > 0 then
    elabVeilDestructAllHyps recursive ignoreHyps
where
  hypsToIgnore : List Name := [``IsSubStateOf, ``IsSubReaderOf, ``Inhabited, ``Nonempty]
  existsBinderName (whnfType : Expr) : MetaM Name := do
    match_expr whnfType with
  | Exists _ body => return body.bindingName!
  | _ => throwError "Expected an existential quantifier, got {whnfType}"
end

elab_rules : tactic
  | `(tactic| veil_destruct $ids:ident*) => elabVeilDestructSpecificHyp ids

/-- Split the goal into sub-goals. -/
elab "veil_destruct_goal" : tactic => withMainContext do
  evalTactic $ ← `(tactic| repeat' constructor)

-- TODO: port `concretize_state` tactic

end Veil
