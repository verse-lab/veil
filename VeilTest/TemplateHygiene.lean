module

public import Lean
public meta import Veil.Frontend.DSL.Module.Util.TemplateHygiene

@[expose, match_pattern] public def templateZero : Nat := 0

open Lean Elab Command in
run_cmd do
  let resolver : Veil.TemplateGlobalResolver := fun name => do
    try
      return some (← liftTermElabM <| resolveGlobalConstNoOverloadCore name)
    catch _ => return none
  let make (name input : String) (resultType : Term) := do
    let .ok parsed := Parser.runParserCategory (← getEnv) `term input
      | throwError "failed to parse hygiene regression: {input}"
    let body ← Veil.specializeTemplateSyntax parsed #[(`base, mkIdent `n)] resolver
    let body : Term := ⟨body⟩
    let name := mkIdent (.mkSimple name)
    let n := mkIdent `n
    elabCommand (← `(command| def $name ($n : Nat) : $resultType := $body))
  make "templateLambda" "(fun n : Nat => base + n) 3" (← `(Nat))
  make "templatePatternLambda" "(fun (n, k) => base + n + k) (1, 2)" (← `(Nat))
  make "templateLet" "let n := 3; base + n" (← `(Nat))
  make "templateFunctionLet" "let f (n : Nat) := base + n; f 3" (← `(Nat))
  make "templateShadowFormal" "let base := 7; base" (← `(Nat))
  make "templateMatch" "match some 3 with | some n => base + n | none => base" (← `(Nat))
  make "templateMatchHyp" "match n : some 3 with | some x => base + x | none => base" (← `(Nat))
  make "templatePatternAlias" "match 1 with | templateZero => 0 | Nat.succ x => base" (← `(Nat))
  make "templateForall" "forall base : Nat, base = base" (← `(Prop))
  make "templateExists" "exists n : Nat, base = n" (← `(Prop))
  make "templateDoLet" "Id.run do let n := 3; return base + n" (← `(Nat))
  make "templateDoArrow" "Id.run do let n <- pure 3; return base + n" (← `(Nat))
  make "templateDoMatch" "Id.run do match some 3 with | some n => return base + n | none => return base" (← `(Nat))
  make "templateDoIf" "Id.run do if n : True then return base else return 0" (← `(Nat))

example (n : Nat) : templateLambda n = n + 3 := rfl
example (n : Nat) : templatePatternLambda n = n + 1 + 2 := rfl
example (n : Nat) : templateLet n = n + 3 := rfl
example (n : Nat) : templateFunctionLet n = n + 3 := rfl
example (n : Nat) : templateShadowFormal n = 7 := rfl
example (n : Nat) : templateMatch n = n + 3 := rfl
example (n : Nat) : templateMatchHyp n = n + 3 := rfl
example (n : Nat) : templatePatternAlias n = n := rfl
example (n : Nat) : templateForall n := fun _ => rfl
example (n : Nat) : templateExists n := ⟨n, rfl⟩
example (n : Nat) : templateDoLet n = n + 3 := rfl
example (n : Nat) : templateDoArrow n = n + 3 := rfl
example (n : Nat) : templateDoMatch n = n + 3 := rfl
example (n : Nat) : templateDoIf n = n := rfl

structure TemplateRecord where
  finalized : Nat

open Lean Elab Command in
run_cmd do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term
      "let source : TemplateRecord := { finalized := 7 }; source.finalized"
    | throwError "failed to parse projection regression"
  let body ← Veil.specializeTemplateSyntax parsed #[(`source.finalized, ← `(99))]
  let body ← Veil.specializeTemplateSyntax body #[(`finalized, ← `(99))]
  let body : Term := ⟨body⟩
  let name := mkIdent `templateLocalProjection
  elabCommand (← `(command| def $name : Nat := $body))

example : templateLocalProjection = 7 := rfl

open Lean Elab Command in
run_cmd do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term "cfg.finalized"
    | throwError "failed to parse structured parameter regression"
  let config ← `(term| ({ finalized := 7 } : TemplateRecord))
  let body ← Veil.specializeTemplateSyntax parsed #[(`cfg, config)]
  let body ← Veil.specializeTemplateSyntax body #[(`finalized, ← `(99))]
  let body : Term := ⟨body⟩
  let name := mkIdent `templateStructuredParameter
  elabCommand (← `(command| def $name : Nat := $body))

example : templateStructuredParameter = 7 := rfl

open Lean Elab Command in
run_cmd do
  let scopedName ← withFreshMacroScope <| MonadQuotation.addMacroScope `source
  let source := mkIdent scopedName
  let projection := mkIdent (scopedName ++ `finalized)
  let expression ← `(term| (fun ($source : TemplateRecord) => $projection)
    ({ finalized := 7 } : TemplateRecord))
  let body ← Veil.specializeTemplateSyntax expression.raw #[(`source.finalized, ← `(99))]
  let body : Term := ⟨body⟩
  let name := mkIdent `templateMacroLocalProjection
  elabCommand (← `(command| def $name : Nat := $body))

example : templateMacroLocalProjection = 7 := rfl

open Lean Elab Command in
run_cmd do
  for (name, input) in #[
      ("templateRecordLabel", "({ finalized := base } : TemplateRecord)"),
      ("templateRecordPun", "({ finalized } : TemplateRecord)")] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `term input
      | throwError "failed to parse record label regression"
    let body ← Veil.specializeTemplateSyntax parsed
      #[(`finalized, ← `(7)), (`base, ← `(7))]
    let body : Term := ⟨body⟩
    let name := mkIdent (.mkSimple name)
    elabCommand (← `(command| def $name : TemplateRecord := $body))

example : templateRecordLabel.finalized = 7 := rfl
example : templateRecordPun.finalized = 7 := rfl

open Lean Elab Command in
run_cmd do
  let literal ← liftTermElabM <| PrettyPrinter.delab (mkNatLit 7)
  let rewritten ← Veil.specializeTemplateSyntax literal #[]
  let body : Term := ⟨rewritten⟩
  let name := mkIdent `templateCanonicalLiteral
  elabCommand (← `(command| def $name : Nat := $body))

example : templateCanonicalLiteral = 7 := rfl

open Lean Elab Command Veil in
run_cmd do
  let .ok parsed := Parser.runParserCategory (← getEnv) `command
      "after_init { r N := N }"
    | throwError "failed to parse implicit assignment binder regression"
  let rewritten ← Veil.specializeTemplateSyntax parsed #[(`r, mkIdent `r_inst)] fun name =>
    pure (if name == `N then some `SomeGlobal.N else none)
  let some assignment := rewritten.find? (·.isOfKind ``Lean.Parser.Term.doReassign)
    | throwError "missing rewritten assignment"
  let `(Lean.Parser.Term.doReassign| $lhs:term := $rhs:term) := assignment
    | throwError "unexpected rewritten assignment"
  let some (_, args) := lhs.isApp? | throwError "missing target coordinate"
  let universal := args[0]!.raw.getId
  unless universal.eraseMacroScopes == `N && universal.hasMacroScopes && rhs.raw.getId == universal do
    throwError "an implicit universal assignment index resolved to the Lean global instead of binding its replacement"

/-- error: active antiquotations in module template quotations are not supported yet -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term "`(term| $base)"
    | throwError "failed to parse active antiquotation regression"
  discard <| Veil.specializeTemplateSyntax parsed #[(`base, mkIdent `n)]

open Lean Elab Command in
run_cmd do
  for input in #["`(term| base)", "`(term| $$base)"] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `term input
      | throwError "failed to parse quotation data regression"
    let rewritten ← Veil.specializeTemplateSyntax parsed #[(`base, mkIdent `n)]
    unless rewritten == parsed do
      throwError "quoted data or escaped antiquotation was changed by module specialization"

namespace TemplatePinnedGlobal
@[expose] public def globalValue : Nat := 7
end TemplatePinnedGlobal

namespace TemplatePinnedCaller

namespace TemplatePinnedGlobal
@[expose] public def globalValue : Nat := 99
end TemplatePinnedGlobal

open Lean Elab Command in
run_cmd do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term
      "TemplatePinnedGlobal.globalValue"
    | throwError "failed to parse pinned global regression"
  let body ← Veil.specializeTemplateSyntax parsed #[] fun name =>
    pure (if name == `TemplatePinnedGlobal.globalValue then some name else none)
  let body : Term := ⟨body⟩
  let name := mkIdent `pinnedTemplateGlobal
  elabCommand (← `(command| def $name : Nat := $body))

example : pinnedTemplateGlobal = 7 := rfl

end TemplatePinnedCaller

open Lean Elab Command Veil in
run_cmd do
  let .ok parsed := Parser.runParserCategory (← getEnv) `command
      "action echo (t : tx) { pure () }"
    | throwError "failed to parse procedure binder regression"
  let rewritten ← Veil.specializeTemplateSyntax parsed #[(`tx, mkIdent ``Nat)]
  unless (rewritten.find? fun s => s.isIdent && s.getId == ``Nat).isSome do
    throwError "procedure argument types were treated as lexical binders"
  if (rewritten.find? fun s => s.isIdent && s.getId.eraseMacroScopes == `tx).isSome then
    throwError "procedure argument type substitution was lost"

open Lean Parser

syntax (name := customTemplateBinder) "custom_bind " ident " => " term : term
syntax (name := customTemplateDoBinder) "custom_do_bind " ident " := " term : doElem

public meta section

open Elab Term

elab_rules : term
  | `(custom_bind $id:ident => $body) => do
    elabTerm (← `(fun ($id : Nat) => $body)) none

/-- error: custom term syntax is not supported in module templates: customTemplateBinder -/
#guard_msgs in
run_cmd do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term "custom_bind n => base"
    | throwError "failed to parse custom binder regression"
  discard <| Veil.specializeTemplateSyntax parsed #[(`base, mkIdent `n)]

@[doElem_elab customTemplateDoBinder]
def customTemplateDoHandler : Lean.Elab.Do.DoElab := fun _ _ =>
  throwUnsupportedSyntax

/-- error: custom statement syntax is not supported in module templates: customTemplateDoBinder -/
#guard_msgs in
run_cmd do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term
      "Id.run do custom_do_bind n := 3; return base"
    | throwError "failed to parse custom statement regression"
  discard <| Veil.specializeTemplateSyntax parsed #[(`base, mkIdent `n)]
