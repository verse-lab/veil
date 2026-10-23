module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Certificate
public meta import Veil.Core.Tools.Synthesizer.Model
public meta import Veil.Core.Tools.Synthesizer.Tactic
public import Veil.Core.Tools.Synthesizer.Soundness

/-!
# The counterexample certificate

When the search finds an execution that violates the property, this file proves, in the module's
namespace,

    theorem Mod.ic3_unsafe : ¬ (∀ th st,
      (Mod.relationalTransitionSystem (Fin n₁) …).reachable th st → Mod.ic3_prop (Fin n₁) … th st)

at the model's sort sizes and typeclass instances.

## Main definitions

* `Veil.Synthesizer.certifyUnsafe`: build and check the counterexample certificate.

## Implementation notes

* The theory and the states are definitions `ic3_cex_th`, `ic3_cex_s0`, … over `Fin n` and the
  concrete types of the enum sorts. A relation is `fun x … ↦ decide (x = a ∧ … ∨ …)` over its
  tuples, a function `fun x … ↦ if x = a ∧ … then b else …` over its rows.
* Each typeclass instance is rebuilt from the model as `ic3_cex_inst_<inst>`, its axioms proven by
  `decide`. The transition system receives each instance by its binder name, since two instances of
  one class at sorts of the same size are both instances at `Fin n`.
* The facts the execution needs (the assumptions, the initial state, each step, the violation) are
  theorems proven by evaluation (`veil_concrete`), and `ic3_unsafe` applies
  `RelationalTransitionSystem.not_invariant_of_reachable`. Nothing rests on the solver.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Command Term Meta Veil Lean.Parser.Term

/-- What a counterexample certificate is built from. -/
structure CexCtx where
  mod : Veil.Module
  sig : Signature
  path : DecodedTrace

namespace CexCtx

variable (c : CexCtx)

/-- The constructors of `s`, if it is an enum sort. -/
def enumCtors? (s : SortName) : Option (Array Name) := (c.sig.enums.find? (·.1 == s)).map (·.2)

/-- The size of an uninterpreted sort in the model. -/
def sortSize (s : SortName) : CommandElabM Nat := do
  let some (_, n) := c.path.sorts.find? (·.1 == s)
    | throwError "IC3: the model does not instantiate sort {s}"
  if n == 0 then throwError "IC3: sort {s} has size 0 in the model"
  return n

/-- The type sort `s` is instantiated at: `Fin n`, or the concrete type of an enum sort. -/
def sortTerm (s : SortName) : CommandElabM Term := do
  if (c.enumCtors? s).isSome then return mkIdent (c.mod.name ++ Name.toEnumConcreteTypeName s)
  `(Fin $(Syntax.mkNumLit (toString (← c.sortSize s))))

/-- Element `k` of sort `s`: `(k : Fin n)`, or the `k`-th constructor of an enum sort. -/
def elementTerm (s : SortName) (k : Nat) : CommandElabM Term := do
  if let some ctors := c.enumCtors? s then
    let some ctor := ctors[k]? | throwError "IC3: enum sort {s} has no constructor at index {k}"
    return mkIdent (c.mod.name ++ Name.toEnumConcreteTypeName s ++ ctor.updatePrefix .anonymous)
  let n ← c.sortSize s
  -- `(k : Fin n)` would reduce modulo `n` and hide a bad index.
  unless k < n do
    throwError "IC3: element {k} of sort {s} is out of range; the model has {n} element(s)"
  `(($(Syntax.mkNumLit (toString k)) : Fin $(Syntax.mkNumLit (toString n))))

/-- `fun (a₀ : s₀) … ↦ body`, or `body` when there are no argument sorts. -/
def lambda (argSorts : Array SortName) (body : Array Term → CommandElabM Term) :
    CommandElabM Term := do
  let args := (Array.range argSorts.size).map fun i ↦ mkIdent (.mkSimple s!"a{i}")
  let b ← body (args.map (·))
  if args.isEmpty then return b
  let binders ← (args.zip argSorts).mapM fun (a, s) ↦ do `(funBinder| ($a : $(← c.sortTerm s)))
  `(fun $binders* ↦ $b)

/-- `a₀ = x₀ ∧ … ∧ aₙ = xₙ` for a row of elements. -/
def rowCondition (args : Array Term) (argSorts : Array SortName) (row : Array Nat) :
    CommandElabM Term := do
  repeatedAnd (← (Array.range row.size).mapM fun i ↦ do
    `($(args[i]!) = $(← c.elementTerm argSorts[i]! row[i]!)))

/-- A relation from its tuples: the disjunction of their conditions, `Bool`-valued when `asBool`. -/
def relationTerm (argSorts : Array SortName) (rows : Array (Array Nat)) (asBool : Bool) :
    CommandElabM Term :=
  c.lambda argSorts fun args ↦ do
    let conds ← rows.mapM fun row ↦
      if row.isEmpty then `(True) else c.rowCondition args argSorts row
    let body ← if conds.isEmpty then `(False) else repeatedOr conds
    if asBool then `(decide $body) else pure body

/-- A function from its rows `(args, value)`, tested in order, the last row's value the final
branch; `fallback` when there are none. -/
def functionTerm (argSorts : Array SortName) (rows : Array (Array Nat × Term)) (fallback : Term) :
    CommandElabM Term :=
  c.lambda argSorts fun args ↦ do
    let mut body := (rows.back?.map (·.2)).getD fallback
    for (row, v) in rows.pop.reverse do
      body ← `(if $(← c.rowCondition args argSorts row) then $v else $body)
    return body

/-- The value of component `sym` in structure `σ`. -/
def componentValue (σ : FinStructure) (sym : Symbol) : CommandElabM Term := do
  let argSorts := if sym.isFunction then sym.argSorts.pop else sym.argSorts
  if sym.isNumeric then
    let rows := ((σ.nums.find? (·.1.key == sym.key)).map (·.2)).getD #[]
    let result := sym.argSorts.back!
    let rows ← rows.mapM fun (args, v) ↦ return (args, ← numeralTerm result v)
    return ← c.functionTerm argSorts rows (← numeralTerm result 0)
  let rows := ((σ.rels.find? (·.1.key == sym.key)).map (·.2)).getD #[]
  if !sym.isFunction then
    if sym.argSorts.isEmpty then return ← if rows.isEmpty then `(false) else `(true)
    return ← c.relationTerm argSorts rows true
  let result := sym.argSorts.back!
  let rows ← rows.mapM fun row ↦ return (row.pop, ← c.elementTerm result (row.back?.getD 0))
  c.functionTerm argSorts rows (← if argSorts.isEmpty then c.elementTerm result 0 else `(default))

/-- The value of an action argument of type `ty` from the model's label. -/
def labelArgTerm (act p : Name) (ty : Term) (v : Option Json) : CommandElabM Term := do
  let .ident _ _ s _ := ty.raw
    | throwError "IC3: action {act} has a parameter of unsupported type {ty}"
  let noValue := m!"IC3: label argument {p} of action {act} has no value in the model"
  if s == ``Bool then
    let some (.bool b) := v | throwError "IC3: label argument {p} of action {act} has no Bool value"
    return ← if b then `(true) else `(false)
  if let some ctors := c.enumCtors? s then
    let some (.str ctor) := v | throwError noValue
    let some k := ctors.findIdx? (ctorBaseName · == ctor)
      | throwError "IC3: label argument {p} of action {act} names no constructor of {s}: {ctor}"
    return ← c.elementTerm s k
  let some (.num k) := v | throwError noValue
  if isNumericSort s then
    unless k.exponent == 0 do
      throwError "IC3: label argument {p} of action {act} is not an integer: {k}"
    if s == `Nat && k.mantissa < 0 then
      throwError "IC3: label argument {p} of action {act} is negative for a Nat parameter: {k}"
    return ← numeralTerm s k.mantissa
  c.elementTerm s k.mantissa.toNat

/-- The label of a step from its JSON (`{"recv": {"sender": 0}}`). -/
def labelTerm (j : Json) : CommandElabM Term := do
  let (act, args) ← match j with
    | .obj kvs =>
      let #[(k, v)] := kvs.toArray | throwError "IC3: unexpected transition label {j}"
      pure (Name.mkSimple k, v)
    | .str k => pure (Name.mkSimple k, Json.obj {})
    | _ => throwError "IC3: unexpected transition label {j}"
  let some a := c.mod.actions.find? (·.name == act)
    | throwError "IC3: transition label names unknown action {act}"
  let (_, params) ← liftTermElabM (c.mod.declarationAllParams a.name a.declarationKind)
  let argTerms ← params.mapM fun p ↦
    c.labelArgTerm act p.name p.type (args.getObjVal? p.name.toString).toOption
  let ctor := mkIdent (labelTypeName ++ a.name)
  if argTerms.isEmpty then return ctor
  `($ctor $argTerms*)

/-- The value of field `field` of a class instance whose table in the model is `rows`. -/
def fieldValue (className field : Name) (rows : Array (Array Nat)) : FieldSpec → CommandElabM Term
  | .relation argSorts isBool => c.relationTerm argSorts rows isBool
  | .constant s => c.elementTerm s ((rows[0]?.bind (·[0]?)).getD 0)
  | .function argSorts s => do
    let rows ← rows.mapM fun row ↦ return (row.pop, ← c.elementTerm s (row.back?.getD 0))
    c.functionTerm argSorts rows (← `(default))
  | .axiom _ => `(by first | decide | (intros; simp_all; done) | (intros; grind))
  | .other => throwError "IC3: field {field} of {className} is neither a relation, a constant, a \
      function between sorts nor an axiom; the counterexample certificate cannot build the instance"

end CexCtx

/-- `{ f₁ := v₁, … }`. -/
def structInstance (fields : Array (Name × Term)) : CommandElabM Term := do
  let items ← fields.mapM fun (f, v) ↦ `(structInstField| $(mkIdent f):ident := $v)
  `({ $items:structInstField,* })

/-- Build and check the counterexample certificate. `property` are the conjuncts of `P`. -/
def certifyUnsafe (mod : Veil.Module) (property : Array Term) (path : DecodedTrace) :
    CommandElabM CertificateResult := do
  let some σ₀ := path.states[0]? | throwError "IC3: empty counterexample"
  throwIfCertified mod [`ic3_unsafe, `ic3_prop]
  let ctx ← liftTermElabM (QueryCtx.ofModule mod)
  let sig ← liftTermElabM (Signature.ofModule mod)
  let c : CexCtx := { mod, sig, path }
  let sortTerms ← sig.sorts.mapM c.sortTerm
  -- The typeclass instances, rebuilt from the model.
  let mut instNames : Array Ident := #[]
  let mut instArgs : Array Term := #[]
  for (inst, className, sortArgs) in sig.instances do
    let specs ← liftTermElabM (Signature.classFieldSpecs inst className sortArgs)
    let fields ← specs.mapM fun (field, spec) ↦ do
      let rows := ((σ₀.rels.find? (·.1.key == inst ++ field)).map (·.2)).getD #[]
      return (field, ← c.fieldValue className field rows spec)
    let name := mkIdent (.mkSimple s!"ic3_cex_inst_{inst}")
    elabChecked (← `(command| instance (priority := high) $name:ident :
      $(mkIdent className) $(← sortArgs.mapM c.sortTerm)* := $(← structInstance fields)))
    instNames := instNames.push name
    -- Each instance is passed by its binder name; instance resolution would pick one for both of
    -- two instances at sorts of the same size.
    instArgs := instArgs.push ⟨(← `(namedArgument| ($(mkIdent inst) := $name))).raw⟩
  -- The theory and the states.
  let thName := mkIdent `ic3_cex_th
  let thFields ← sig.theorySymbols.mapM fun sym ↦ return (sym.name, ← c.componentValue σ₀ sym)
  elabChecked (← `(command|
    def $thName : @$(mkIdent theoryName) $sortTerms* := $(← structInstance thFields)))
  let stateT ← `($(mkIdent stateName) ($fieldAbstractDispatcher $sortTerms*))
  let stateNames := (Array.range path.states.size).map (mkIdent <| .mkSimple s!"ic3_cex_s{·}")
  for (σ, name) in path.states.zip stateNames do
    let fields ← sig.stateSymbols.mapM fun sym ↦ return (sym.name, ← c.componentValue σ sym)
    elabChecked (← `(command| def $name : $stateT := $(← structInstance fields)))
  let propName := mkIdent `ic3_prop
  definePredicate ctx propName property
  -- An enum constant in an action is a field of the enum's class, which `simp` does not unfold
  -- to the constructor; these equations do.
  let mut enumEqs : Array Ident := #[]
  for (s, ctors) in sig.enums do
    for (ctor, k) in ctors.zipIdx do
      let base := ctor.updatePrefix .anonymous
      let eqName := mkIdent (.mkSimple s!"ic3_cex_enum_{s}_{base}")
      let lhs ← `(($(mkIdent (Name.toEnumClass s ++ base)) : $(← c.sortTerm s)))
      elabChecked (← `(command| theorem $eqName : $lhs = $(← c.elementTerm s k) := rfl))
      enumEqs := enumEqs.push eqName
  -- The facts of the execution, each proven by evaluation.
  let rts ← `($(mkIdent assembledRTSName) $sortTerms* $instArgs*)
  let prop ← `($propName $sortTerms* $instArgs*)
  let defs := #[thName] ++ stateNames ++ instNames ++ enumEqs
  let fact (name : Ident) (stmt : Term) (unfolds : Array Ident) : CommandElabM Unit := do
    elabChecked (← `(command| theorem $name : $stmt := by
      unfold $[$unfolds:ident]*
      try veil_simp +$(mkIdent `instances) only [$(mkIdent `nextSimp):ident]
      all_goals veil_concrete [$defs,*]))
  let rtsName := mkIdent (mod.name ++ assembledRTSName)
  let hasName := mkIdent `ic3_cex_assumptions
  fact hasName (← `(term| ($rts).$(mkIdent `assumptions) $thName))
    #[rtsName, mkIdent (mod.name ++ `Assumptions)]
  let initName := mkIdent `ic3_cex_init
  fact initName (← `(term| ($rts).$(mkIdent `init) $thName $(stateNames[0]!)))
    #[rtsName, mkIdent (mod.name ++ `Init)]
  let mut reach ← `(.init _ $hasName $initName)
  for i in [1:path.states.size] do
    let lbl ← c.labelTerm path.labels[i]!
    let stepName := mkIdent (.mkSimple s!"ic3_cex_step_{i - 1}")
    let step ← `(term| ($rts).$(mkIdent `tr) $thName $(stateNames[i - 1]!) $lbl $(stateNames[i]!))
    fact stepName step #[rtsName, mkIdent (mod.name ++ `Next)]
    reach ← `(.step _ _ $reach (Exists.intro $lbl $stepName))
  let badName := mkIdent `ic3_cex_bad
  fact badName (← `(¬ ($prop) $thName $(stateNames.back!))) #[propName]
  let thmName := mkIdent `ic3_unsafe
  let (th, st) := (mkIdent `th, mkIdent `st)
  elabChecked (← `(command|
    theorem $thmName : ¬ (∀ ($th : @$(mkIdent theoryName) $sortTerms*) ($st : $stateT),
        ($rts).$(mkIdent `reachable) $th $st → ($prop) $th $st) :=
      Veil.RelationalTransitionSystem.not_invariant_of_reachable (sys := $rts) (p := $prop) $reach
        $badName))
  liftCoreM <| certificateResult (mod.name ++ thmName.getId) (mod.name ++ propName.getId)

end Veil.Synthesizer
