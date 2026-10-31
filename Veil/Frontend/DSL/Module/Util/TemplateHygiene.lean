module

public meta import Veil.Frontend.DSL.Module.Syntax
public meta import Veil.Frontend.DSL.Action.Syntax
public meta import Veil.Util.Meta

public meta section

open Lean Elab Command

namespace Veil

/-- The lexical module context can resolve free names before occurrence
specialization. A binder or explicit substitution always takes precedence. -/
abbrev TemplateGlobalResolver := Name → CommandElabM (Option Name)

private abbrev Locals := Array (Name × Syntax)

private def lookupLocal (locals : Locals) (name : Name) : Option Syntax :=
  locals.findSomeRev? fun (original, replacement) =>
    if original == name then some replacement else none

/-- A qualified surface identifier can be a projection from a local which
shadows a module reference. Resolve that lexical prefix before dependency
substitution, and make the projection explicit for Lean's elaborator. -/
private partial def localProjection? (locals : Locals) (name : Name) :
    CommandElabM (Option Syntax) := do
  if let some localId := lookupLocal locals name then return some localId
  let view := extractMacroScopes name
  let .str stem field := view.name | return none
  let stem := { view with name := stem }.review
  let some base ← localProjection? locals stem | return none
  let base : Term := ⟨base⟩
  return some (← `(term| ($base).$(mkIdent (.mkSimple field)))).raw

private partial def bindingProjection? (bindings : Array (Name × Term)) (name : Name) :
    CommandElabM (Option Syntax) := do
  if let some (_, value) := bindings.find? (·.1 == name) then return some value.raw
  let view := extractMacroScopes name
  let .str stem field := view.name | return none
  let stem := { view with name := stem }.review
  let some base ← bindingProjection? bindings stem | return none
  let base : Term := ⟨base⟩
  return some (← `(term| ($base).$(mkIdent (.mkSimple field)))).raw

private def freshBinder (stx : Syntax) : CommandElabM Syntax := do
  let name ← withFreshMacroScope <| MonadQuotation.addMacroScope stx.getId
  return mkIdentFrom stx name

private def bindIdent (id : Syntax) (locals : Locals) : CommandElabM (Syntax × Locals) := do
  if !id.isIdent || id.getId == `_ then return (id, locals)
  let fresh ← freshBinder id
  return (fresh, locals.push (id.getId, fresh))

private def updateArgs (stx : Syntax) (args : Array Syntax) : Syntax :=
  match stx with
  | .node info kind _ => .node info kind args
  | _ => stx

private def isBracketedBinder (stx : Syntax) : Bool :=
  [``Lean.Parser.Term.explicitBinder, ``Lean.Parser.Term.implicitBinder,
   ``Lean.Parser.Term.strictImplicitBinder, ``Lean.Parser.Term.instBinder].contains stx.getKind

private def isProcedureCommand (stx : Syntax) : Bool :=
  [``procedureDefinition, ``procedureDefinitionWithSpec, ``transitionDefinition].contains stx.getKind

private def isDoSequence (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Term.doSeqIndent || stx.isOfKind ``Lean.Parser.Term.doSeqBracketed

private def isQuotation (stx : Syntax) : Bool := stx.isQuot

private partial def rejectActiveAntiquotations (stx : Syntax) (quoted := false) :
    CommandElabM Unit := do
  if quoted && stx.isAntiquot && !stx.isEscapedAntiquot then
    throwErrorAt stx "active antiquotations in module template quotations are not supported yet"
  let childQuoted := Action.childrenAreQuoted stx quoted
  for child in stx.getArgs do rejectActiveAntiquotations child childQuoted

/-- An already resolved global must not be looked up relative to the caller's
namespace again. A caller can have a different declaration under the same
qualified suffix, so ordinary qualification alone is insufficient. -/
private def pinnedGlobalIdent (origin : Syntax) (name : Name) : Syntax :=
  match mkIdentFrom origin (`_root_ ++ name) with
  | ⟨.ident info raw spelling _⟩ => .ident info raw spelling [.decl name []]
  | id => id.raw

private def preResolvedConstants (stx : Syntax) : List Name :=
  match stx with
  | .ident _ _ _ pre => pre.filterMap fun
      | .decl name [] => some name
      | _ => none
  | _ => []

/-- Macros can expose their scopes through the ordinary core binding forms.
An arbitrary elaborator can bind identifiers in an opaque way, so it cannot
participate in syntax specialization without an explicit adapter. -/
private def rejectOpaqueElaborator (stx : Syntax) : CommandElabM Unit := do
  let kind := stx.getKind
  let veilTerm := [``oldTerm].contains kind
  let veilStatement := [``requireDo, ``assertDo, ``ensureDo,
    `Veil.Action.DoElab.saveEntryState, `Veil.Action.DoElab.theoryOpen,
    `Veil.Action.DoElab.internalExpr, `Veil.Action.DoElab.stateAssignWrapper].contains kind
  let env ← getEnv
  let termHandlers := Lean.Elab.Term.termElabAttribute.getEntries env kind
  let customTermHandler := termHandlers.any fun handler => !(`Lean.Elab).isPrefixOf handler.declName
  let statementHandlers := Lean.Elab.Do.doElemElabAttribute.getEntries env kind
  let customStatementHandler := statementHandlers.any fun handler =>
    !(`Lean.Elab).isPrefixOf handler.declName &&
    !((`Veil.Action.DoElab).isPrefixOf handler.declName &&
      ((`Lean.Parser.Term).isPrefixOf kind || veilStatement))
  if customTermHandler && !veilTerm then
    throwErrorAt stx "custom term syntax is not supported in module templates: {kind}"
  if customStatementHandler && !veilStatement then
    throwErrorAt stx "custom statement syntax is not supported in module templates: {kind}"

mutual
  /-- Alpha-renaming prevents caller argument syntax from becoming captured
  when it is inserted below a template binder. Inserted substitutions are
  returned directly and are never rewritten through the template's locals. -/
  private partial def rewrite (stx : Syntax) (bindings : Array (Name × Term))
      (resolve : TemplateGlobalResolver) (locals : Locals) : CommandElabM Syntax := do
    if isQuotation stx then
      rejectActiveAntiquotations stx
      return stx
    if stx.isIdent then
      if let some id ← localProjection? locals stx.getId then return id
      if let some value ← bindingProjection? bindings stx.getId then return value
      -- Expanded notation carries already resolved declarations, often with
      -- macro-scoped surface names. Preserve that candidate list rather than
      -- trying to resolve its synthetic spelling in another namespace.
      if let .ident _ _ _ pre := stx then
        unless pre.isEmpty do return stx
      if let some globalName ← resolve stx.getId then return pinnedGlobalIdent stx globalName
      return stx
    if stx.getKind == `hygieneInfo then return stx
    if let some assignment ← rewriteAssignment? stx bindings resolve locals then
      return assignment
    if stx.isOfKind ``Lean.Parser.Term.namedArgument then
      return stx.setArg 3 (← rewrite stx[3] bindings resolve locals)
    if stx.isOfKind ``Lean.Parser.Term.proj then
      return stx.setArg 0 (← rewrite stx[0] bindings resolve locals)
    if stx.isOfKind ``Lean.Parser.Term.structInstLVal then return stx
    if stx.isOfKind ``Lean.Parser.Term.structInstField then
      let value := stx[1]
      if value.getArgs.isEmpty then
        unless stx[0][1].getArgs.isEmpty do
          throwErrorAt stx "qualified field puns in module templates are not supported yet"
        let rhs ← rewrite stx[0][0] bindings resolve locals
        let definition := mkNode ``Lean.Parser.Term.structInstFieldDef
          #[mkAtom ":=", mkNullNode #[], rhs]
        return stx.setArg 1 (mkNullNode #[mkNullNode #[], mkNullNode #[], definition])
      let mut parts := value.getArgs
      let (params, fieldLocals) ← rewriteBinderContainer parts[0]! bindings resolve locals
      parts := parts.set! 0 params
      for i in [1:parts.size] do
        parts := parts.set! i (← rewrite parts[i]! bindings resolve fieldLocals)
      return stx.setArg 1 (updateArgs value parts)
    if isProcedureCommand stx then
      let mut args := stx.getArgs
      args := args.set! 1 (← rewrite args[1]! bindings resolve locals)
      let (binders, bodyLocals) ← rewriteBinderContainer args[2]! bindings resolve locals
      args := args.set! 2 binders
      for i in [3:args.size] do
        args := args.set! i (← rewrite args[i]! bindings resolve bodyLocals)
      return updateArgs stx args
    if stx.isOfKind ``stateComponentDeclaration then
      let mut args := stx.getArgs
      args := args.set! 2 (← rewrite args[2]! bindings resolve locals)
      let (binders, bodyLocals) ← rewriteBinderContainer args[3]! bindings resolve locals
      args := args.set! 3 binders
      for i in [4:args.size] do
        args := args.set! i (← rewrite args[i]! bindings resolve bodyLocals)
      return updateArgs stx args
    if stx.isOfKind ``Lean.Parser.Term.forall then
      let mut args := stx.getArgs
      -- The shared annotation in `forall x y : T, ...` is outside x/y.
      args := args.set! 2 (← rewrite args[2]! bindings resolve locals)
      let (binders, bodyLocals) ← rewriteBinderContainer args[1]! bindings resolve locals
      args := args.set! 1 binders
      args := args.set! 4 (← rewrite args[4]! bindings resolve bodyLocals)
      return updateArgs stx args
    if stx.isOfKind ``Lean.Parser.Term.basicFun then
      let mut args := stx.getArgs
      let (expandedBinders, expandedBody, _) ← liftMacroM <|
        Lean.Elab.Term.expandFunBinders args[0]!.getArgs args[3]!
      args := args.set! 0 (updateArgs args[0]! expandedBinders)
      args := args.set! 3 expandedBody
      let (binders, bodyLocals) ← rewriteBinderContainer args[0]! bindings resolve locals
      -- `expandFunBinders` produces elaborator-only explicitBinder nodes.
      -- Lambda syntax uses ordinary type-ascription terms in that slot;
      -- restore that surface shape so specialized arguments can also be
      -- parenthesized/printed by subsequent declaration generation.
      let mut surfaceBinders := #[]
      for binder in binders.getArgs do
        if binder.isOfKind ``Lean.Parser.Term.explicitBinder then
          let tp : Term := ⟨binder[2][1]⟩
          for id in binder[1].getArgs do
            let id : Term := ⟨id⟩
            surfaceBinders := surfaceBinders.push (← `(term| ($id : $tp))).raw
        else
          surfaceBinders := surfaceBinders.push binder
      args := args.set! 0 (updateArgs binders surfaceBinders)
      for i in [1:args.size] do
        args := args.set! i (← rewrite args[i]! bindings resolve bodyLocals)
      return updateArgs stx args
    if [``Lean.Parser.Term.let, ``Lean.Parser.Term.have,
        ``Lean.Parser.Term.haveI, ``Lean.Parser.Term.letI].contains stx.getKind then
      let mut args := stx.getArgs
      let (decl, bodyLocals) ← rewriteLetDecl args[2]! bindings resolve locals
      args := args.set! 2 decl
      args := args.set! 4 (← rewrite args[4]! bindings resolve bodyLocals)
      return updateArgs stx args
    if isDoSequence stx then return (← rewriteSequence stx bindings resolve locals).1
    if stx.isOfKind ``Lean.Parser.Term.doIf then
      return ← rewriteDoIf stx bindings resolve locals
    if stx.getKind == `termDepIfThenElse then
      let mut args := stx.getArgs
      let binder := args[1]!
      let (id, branchLocals) ← bindIdent binder[0] locals
      args := args.set! 1 (binder.setArg 0 id)
      args := args.set! 3 (← rewrite args[3]! bindings resolve locals)
      args := args.set! 5 (← rewrite args[5]! bindings resolve branchLocals)
      args := args.set! 7 (← rewrite args[7]! bindings resolve branchLocals)
      return updateArgs stx args
    if stx.isOfKind ``Lean.Parser.Term.match || stx.isOfKind ``Lean.Parser.Term.doMatch then
      let mut args := stx.getArgs
      let some discrIndex := args.findIdx? fun arg =>
          arg.getArgs.any (·.isOfKind ``Lean.Parser.Term.matchDiscr)
        | throwErrorAt stx "unsupported match discriminants in module template"
      let (discrs, branchLocals) ← rewriteDiscriminants args[discrIndex]! bindings resolve locals
      args := args.set! discrIndex discrs
      for i in [0:args.size] do
        if i != discrIndex then
          args := args.set! i (← rewrite args[i]! bindings resolve branchLocals)
      return updateArgs stx args
    if stx.isOfKind ``Lean.Parser.Term.matchAlt then
      let mut args := stx.getArgs
      let (patterns, branchLocals) ← rewritePattern args[1]! bindings resolve locals
      args := args.set! 1 patterns
      args := args.set! 3 (← rewrite args[3]! bindings resolve branchLocals)
      return updateArgs stx args
    -- Binder macros such as Exists expand into ordinary lambdas. This also
    -- gives imported notation the expansion environment of its declaration.
    if let some (_, expanded?) ← liftMacroM <| expandMacroImpl? (← getEnv) stx then
      let expanded ← liftMacroM <| liftExcept expanded?
      return ← rewrite expanded bindings resolve locals
    if [``Lean.Parser.Term.byTactic, ``Lean.Parser.Term.suffices,
        ``Lean.Parser.Term.letrec, ``Lean.Parser.Term.matchExpr,
        ``Lean.Parser.Term.letExpr].contains stx.getKind then
      throwErrorAt stx "this binding form is not supported in module templates yet"
    rejectOpaqueElaborator stx
    -- A binder which reaches generic traversal has no known lexical scope.
    -- Fail closed rather than accidentally inserting an argument under it.
    if isBracketedBinder stx || stx.isOfKind ``Lean.Parser.Term.binderIdent ||
        stx.getKind == `Lean.binderIdent then
      throwErrorAt stx "unsupported binding form in module template; use an ordinary forall, fun, let, match, or procedure parameter"
    let args ← stx.getArgs.mapM fun arg => rewrite arg bindings resolve locals
    return updateArgs stx args

  /-- Rewrite a binder list from left to right. Types can refer to earlier
  binders; declaration identifiers are alpha-renamed, never substituted. -/
  private partial def rewriteBinderContainer (stx : Syntax) (bindings : Array (Name × Term))
      (resolve : TemplateGlobalResolver) (locals : Locals) : CommandElabM (Syntax × Locals) := do
    if isQuotation stx then
      rejectActiveAntiquotations stx
      return (stx, locals)
    if stx.getKind == `hygieneInfo then return (stx, locals)
    if stx.getKind == `Lean.bracketedExplicitBinders then
      let mut args := stx.getArgs
      let mut ids := #[]
      let mut bodyLocals := locals
      for id in args[1]!.getArgs do
        let (id, next) ← rewriteBinderContainer id bindings resolve bodyLocals
        ids := ids.push id
        bodyLocals := next
      args := args.set! 1 (updateArgs args[1]! ids)
      args := args.set! 3 (← rewrite args[3]! bindings resolve locals)
      return (updateArgs stx args, bodyLocals)
    if stx.isIdent then return ← bindIdent stx locals
    if stx.getKind == `Lean.binderIdent || stx.isOfKind ``Lean.Parser.Term.binderIdent then
      let (id, locals) ← bindIdent stx[0] locals
      return (stx.setArg 0 id, locals)
    if isBracketedBinder stx then
      let mut args := stx.getArgs
      let outer := locals
      let mut bodyLocals := locals
      if stx.isOfKind ``Lean.Parser.Term.instBinder then
        -- Instance binder's optional name occupies a distinct parser shape.
        throwErrorAt stx "named instance binders in module templates are not supported yet"
      let mut ids := #[]
      for id in args[1]!.getArgs do
        let (id, next) ← rewriteBinderContainer id bindings resolve bodyLocals
        ids := ids.push id
        bodyLocals := next
      args := args.set! 1 (updateArgs args[1]! ids)
      for i in [2:args.size] do
        args := args.set! i (← rewrite args[i]! bindings resolve outer)
      return (updateArgs stx args, bodyLocals)
    if stx.isOfKind ``Lean.Parser.Term.typeAscription then
      let mut args := stx.getArgs
      let (pattern, bodyLocals) ← rewritePattern args[1]! bindings resolve locals
      args := args.set! 1 pattern
      args := args.set! 3 (← rewrite args[3]! bindings resolve locals)
      return (updateArgs stx args, bodyLocals)
    let mut args := #[]
    let mut bodyLocals := locals
    for arg in stx.getArgs do
      let (arg, next) ← rewriteBinderContainer arg bindings resolve bodyLocals
      args := args.push arg
      bodyLocals := next
    return (updateArgs stx args, bodyLocals)

  /-- Only bare, unbound capitals in target coordinates are Ivy universal
  indices. Fixed-coordinate expressions are evaluated outside that scope;
  the pure replacement expression is evaluated inside it. Lean globals do
  not change this classification. -/
  private partial def rewriteAssignmentTarget (lhs : Term) (bindings : Array (Name × Term))
      (resolve : TemplateGlobalResolver) (locals : Locals) :
      CommandElabM (Term × Locals × Bool) := do
    let some (head, args) := lhs.isApp?
      | return (⟨← rewrite lhs.raw bindings resolve locals⟩, locals, false)
    let head : Term := ⟨← rewrite head.raw bindings resolve locals⟩
    let mut replacementLocals := locals
    let mut rewrittenArgs : Array Term := #[]
    let mut hasUniversals := false
    for arg in args do
      if arg.raw.isIdent && isCapital arg.raw.getId &&
          (lookupLocal locals arg.raw.getId).isNone &&
          !(bindings.any (·.1 == arg.raw.getId)) then
        hasUniversals := true
        let id ← match lookupLocal replacementLocals arg.raw.getId with
          | some id => pure id
          | none => freshBinder arg.raw
        replacementLocals := replacementLocals.push (arg.raw.getId, id)
        rewrittenArgs := rewrittenArgs.push ⟨id⟩
      else
        rewrittenArgs := rewrittenArgs.push ⟨← rewrite arg.raw bindings resolve locals⟩
    return (Syntax.mkApp head rewrittenArgs, replacementLocals, hasUniversals)

  private partial def rewriteAssignment? (stx : Syntax) (bindings : Array (Name × Term))
      (resolve : TemplateGlobalResolver) (locals : Locals) : CommandElabM (Option Syntax) := do
    if stx.isOfKind ``Lean.Parser.Term.doReassignArrow then
      let decl := stx[0]
      if decl.isOfKind ``Lean.Parser.Term.doIdDecl || decl.isOfKind ``Lean.Parser.Term.doPatDecl then
        let (lhs, _, _) ← rewriteAssignmentTarget ⟨decl[0]⟩ bindings resolve locals
        let mut parts := decl.getArgs
        parts := parts.set! 0 lhs.raw
        for i in [1:parts.size] do
          parts := parts.set! i (← rewrite parts[i]! bindings resolve locals)
        return some (stx.setArg 0 (updateArgs decl parts))
    match stx with
    | `(Lean.Parser.Term.doReassign| $lhs:term $[: $ty:term]? := $rhs:term) =>
      let (lhs, replacementLocals, hasUniversals) ← rewriteAssignmentTarget lhs bindings resolve locals
      if hasUniversals && (Action.findOutsideQuotations? rhs.raw fun child =>
          if child.isOfKind ``Lean.Parser.Term.nestedAction then some () else none).isSome then
        throwErrorAt rhs "nested actions in a universally indexed module assignment are not supported; bind the result before the assignment"
      let rhs : Term := ⟨← rewrite rhs.raw bindings resolve replacementLocals⟩
      let ty ← ty.mapM fun ty => return (⟨← rewrite ty.raw bindings resolve locals⟩ : Term)
      return some (← `(Lean.Parser.Term.doReassign| $lhs:term $[: $ty:term]? := $rhs:term)).raw
    | `(doElem| $lhs:term := *) =>
      let (lhs, _, _) ← rewriteAssignmentTarget lhs bindings resolve locals
      return some (← `(doElem| $lhs:term := *)).raw
    | _ => return none

  private partial def rewritePattern (stx : Syntax) (bindings : Array (Name × Term))
      (resolve : TemplateGlobalResolver) (locals : Locals) : CommandElabM (Syntax × Locals) := do
    if stx.isIdent then
      if let some id := lookupLocal locals stx.getId then return (id, locals)
      let resolved ← match preResolvedConstants stx with
        | [] => resolve stx.getId
        | [name] => pure (some name)
        | _ => throwErrorAt stx "overloaded pattern constants in module templates must be qualified explicitly"
      if let some name := resolved then
        let env ← getEnv
        if env.isConstructor name || hasMatchPatternAttribute env name then
          return (pinnedGlobalIdent stx name, locals)
      -- Repeated names in alternative patterns denote the same binder.
      return ← bindIdent stx locals
    if isQuotation stx then
      rejectActiveAntiquotations stx
      return (stx, locals)
    if stx.getKind == `hygieneInfo then return (stx, locals)
    if stx.isOfKind ``Lean.Parser.Term.inaccessible then
      let args ← stx.getArgs.mapM fun arg => rewrite arg bindings resolve locals
      return (updateArgs stx args, locals)
    if stx.isOfKind ``Lean.Parser.Term.typeAscription then
      let mut args := stx.getArgs
      let (pattern, bodyLocals) ← rewritePattern args[1]! bindings resolve locals
      args := args.set! 1 pattern
      args := args.set! 3 (← rewrite args[3]! bindings resolve locals)
      return (updateArgs stx args, bodyLocals)
    let mut args := #[]
    let mut bodyLocals := locals
    for arg in stx.getArgs do
      let (arg, next) ← rewritePattern arg bindings resolve bodyLocals
      args := args.push arg
      bodyLocals := next
    return (updateArgs stx args, bodyLocals)

  private partial def rewriteDiscriminants (stx : Syntax) (bindings : Array (Name × Term))
      (resolve : TemplateGlobalResolver) (locals : Locals) : CommandElabM (Syntax × Locals) := do
    let mut args := #[]
    let mut branchLocals := locals
    for discr in stx.getArgs do
      unless discr.isOfKind ``Lean.Parser.Term.matchDiscr do
        throwErrorAt discr "unsupported match discriminant in module template"
      let mut parts := discr.getArgs
      let binder := parts[0]!
      unless binder.getArgs.isEmpty do
        let (id, next) ← bindIdent binder[0] branchLocals
        branchLocals := next
        parts := parts.set! 0 (binder.setArg 0 id)
      parts := parts.set! 1 (← rewrite parts[1]! bindings resolve locals)
      args := args.push (updateArgs discr parts)
    return (updateArgs stx args, branchLocals)

  private partial def rewriteLetDecl (stx : Syntax) (bindings : Array (Name × Term))
      (resolve : TemplateGlobalResolver) (locals : Locals) : CommandElabM (Syntax × Locals) := do
    if stx.isOfKind ``Lean.Parser.Term.letDecl then
      let (decl, bodyLocals) ← rewriteLetDecl stx[0] bindings resolve locals
      return (stx.setArg 0 decl, bodyLocals)
    let mut args := stx.getArgs
    if stx.isOfKind ``Lean.Parser.Term.letIdDecl then
      let (name, bodyLocals) ← bindIdent args[0]![0] locals
      args := args.set! 0 (args[0]!.setArg 0 name)
      let (params, rhsLocals) ← rewriteBinderContainer args[1]! bindings resolve locals
      args := args.set! 1 params
      args := args.set! 2 (← rewrite args[2]! bindings resolve rhsLocals)
      args := args.set! 4 (← rewrite args[4]! bindings resolve rhsLocals)
      return (updateArgs stx args, bodyLocals)
    if stx.isOfKind ``Lean.Parser.Term.letPatDecl then
      let (pattern, bodyLocals) ← rewritePattern args[0]! bindings resolve locals
      args := args.set! 0 pattern
      args := args.set! 2 (← rewrite args[2]! bindings resolve locals)
      args := args.set! 4 (← rewrite args[4]! bindings resolve locals)
      return (updateArgs stx args, bodyLocals)
    throwErrorAt stx "unsupported let declaration in module template"

  private partial def rewriteStatement (stx : Syntax) (bindings : Array (Name × Term))
      (resolve : TemplateGlobalResolver) (locals : Locals) : CommandElabM (Syntax × Locals) := do
    if let some (_, expanded?) ← liftMacroM <| expandMacroImpl? (← getEnv) stx then
      let expanded ← liftMacroM <| liftExcept expanded?
      return ← rewriteStatement expanded bindings resolve locals
    if stx.isOfKind ``Lean.Parser.Term.doLet || stx.isOfKind ``Lean.Parser.Term.doHave then
      let mut args := stx.getArgs
      let some i := args.findIdx? (·.isOfKind ``Lean.Parser.Term.letDecl)
        | throwErrorAt stx "unsupported local declaration in module template"
      let (decl, bodyLocals) ← rewriteLetDecl args[i]! bindings resolve locals
      args := args.set! i decl
      return (updateArgs stx args, bodyLocals)
    if stx.isOfKind ``Lean.Parser.Term.doLetArrow then
      let mut args := stx.getArgs
      let some i := args.findIdx? fun arg =>
          arg.isOfKind ``Lean.Parser.Term.doIdDecl || arg.isOfKind ``Lean.Parser.Term.doPatDecl
        | throwErrorAt stx "unsupported monadic declaration in module template"
      let decl := args[i]!
      let mut parts := decl.getArgs
      let (pattern, bodyLocals) ← if decl.isOfKind ``Lean.Parser.Term.doIdDecl then
          bindIdent parts[0]! locals
        else rewritePattern parts[0]! bindings resolve locals
      parts := parts.set! 0 pattern
      for j in [1:parts.size] do
        parts := parts.set! j (← rewrite parts[j]! bindings resolve locals)
      args := args.set! i (updateArgs decl parts)
      return (updateArgs stx args, bodyLocals)
    if [``Lean.Parser.Term.doLetElse, ``Lean.Parser.Term.doLetRec,
        ``Lean.Parser.Term.doFor].contains stx.getKind then
      throwErrorAt stx "this local binding form is not supported in module templates yet"
    return (← rewrite stx bindings resolve locals, locals)

  private partial def rewriteSequence (stx : Syntax) (bindings : Array (Name × Term))
      (resolve : TemplateGlobalResolver) (locals : Locals) : CommandElabM (Syntax × Locals) := do
    if stx.isOfKind ``Lean.Parser.Term.doSeqItem then
      let (statement, bodyLocals) ← rewriteStatement stx[0] bindings resolve locals
      return (stx.setArg 0 statement, bodyLocals)
    let mut args := #[]
    let mut bodyLocals := locals
    for arg in stx.getArgs do
      let (arg, next) ← rewriteSequence arg bindings resolve bodyLocals
      args := args.push arg
      bodyLocals := next
    return (updateArgs stx args, bodyLocals)

  private partial def rewriteDoIf (stx : Syntax) (bindings : Array (Name × Term))
      (resolve : TemplateGlobalResolver) (locals : Locals) : CommandElabM Syntax := do
    let mut args := stx.getArgs
    let cond := args[1]!
    unless cond.isOfKind ``Lean.Parser.Term.doIfProp do
      throwErrorAt cond "pattern-binding if conditions are not supported in module templates yet"
    let mut condArgs := cond.getArgs
    let mut branchLocals := locals
    let binder := condArgs[0]!
    unless binder.getArgs.isEmpty do
      let (id, next) ← bindIdent binder[0] locals
      branchLocals := next
      condArgs := condArgs.set! 0 (binder.setArg 0 id)
    condArgs := condArgs.set! 1 (← rewrite condArgs[1]! bindings resolve locals)
    args := args.set! 1 (updateArgs cond condArgs)
    for i in [2:args.size] do
      args := args.set! i (← rewrite args[i]! bindings resolve branchLocals)
    return updateArgs stx args
end

/-- Specialize a template declaration with hygienic local binders. The
resolver, when supplied, pins free constants in the template's lexical scope.
Occurrence fields and caller arguments are inserted only after resolution. -/
def specializeTemplateSyntax (stx : Syntax) (bindings : Array (Name × Term))
    (resolveGlobal : TemplateGlobalResolver := fun _ => pure none) : CommandElabM Syntax :=
  rewrite stx bindings resolveGlobal #[]

end Veil
