module

public import Veil

/-! Symbolic counterexamples retain ordinary module arguments, in declaration
order, across state/theory/label construction. Check the structured counterexample
and the actual reconstructed parameter values, including class dictionaries. -/

set_option veil.smt.trust false
set_option veil.printCounterexamples false

open Lean Elab Command Meta

open Lean Elab Command Meta in
private meta def counterexampleField (record : Json) (name : String) : CommandElabM Json := do
  let .ok fields := (record.getObjValD "fields").getArr? | throwError "missing record fields: {record}"
  let some field := fields.find? (fun field => field.getObjValD "name" == toJson name)
    | throwError "missing field {name}: {record}"
  return field.getObjValD "value"

open Lean Elab Command in
private meta def counterexampleNat (value : Json) : CommandElabM Nat := do
  let .ok value := value.getNat? | throwError "expected a natural number, got {value}"
  return value

open Lean Elab Command in
private meta def counterexampleMapAt (map key : Json) : CommandElabM Json := do
  let .ok entries := (map.getObjValD "entries").getArr? | throwError "missing map entries: {map}"
  let some entry := entries.find? (fun entry => entry.getObjValD "key" == key)
    | throwError "missing map key {key}: {map}"
  return entry.getObjValD "value"

open Lean Meta in
private meta def reconstructedNatJson (value : Expr) : MetaM Json := do
  let ty ← whnf (← inferType value)
  let value ← if ty.isAppOf ``Fin then mkAppM ``Fin.val #[value] else pure value
  let value ← reduce value
  let .lit (.natVal n) := value | throwError "expected reconstructed numeral, got {value}"
  return toJson n

veil module CexLedger

type tenant
param ceiling : Nat
function granted : tenant → Nat
after_init { granted T := 0 }

action issue (t : tenant) {
  require granted t < ceiling
  granted t := granted t + 1
}

action revoke (t : tenant) {
  require 0 < granted t
  granted t := granted t - 1
}

invariant [within_ceiling] ∀ t : tenant, granted t ≤ ceiling
#gen_spec
end CexLedger

veil module CexAccount

type tenant
param ceiling : Nat
param owner : tenant
param ledger : CexLedger tenant ceiling
individual used : Nat
after_init { used := 0 }

action acquire {
  require used < ledger.granted owner
  used := used + 1
}

invariant [grant_backed] used ≤ ledger.granted owner
#gen_spec
end CexAccount

veil module CexComposition

type tenant
param owner : tenant
param other : tenant
isolate ledger : CexLedger (tenant := tenant) (ceiling := 2)
isolate account : CexAccount (tenant := tenant) (ceiling := 2)
  (owner := owner) (ledger := ledger) with ledger

assumption [owners_differ] owner ≠ other

safety [no_overdraw] account.used ≤ ledger.granted owner

#gen_spec

#guard_msgs(drop info, drop warning) in
set_option veil.violationIsError false in
#check_invariants

run_cmd do
  let results ← Veil.Verifier.waitEnabledSync
  let mod ← Veil.getCurrentModule
  let nameFor (name : Name) := (mod.instanceNames.find? (·.1 == name)).map (·.2)
  let some revoke := nameFor `ledger.revoke | throwError "missing revoke action"
  let some backed := nameFor `account.grant_backed | throwError "missing account invariant"
  let some granted := nameFor `ledger.granted | throwError "missing granted field"
  let some used := nameFor `account.used | throwError "missing used field"
  let mut sawWP := false
  let mut sawTR := false
  for vc in results.vcs do
    let .induction metadata := vc.metadata | continue
    unless metadata.action == revoke && metadata.property == backed do continue
    unless vc.status == some .disproven do throwError "revocation was not disproven"
    for d in vc.timing.dischargers do
      let some (.disproven (some (.sat models)) _) := d.result | continue
      for model in models do
        let some model := model | throwError "missing structured revocation counterexample"
        let json := model.structuredJson
        let owner := (json.getObjValD "extraVals").getObjValD "owner"
        let other := (json.getObjValD "extraVals").getObjValD "other"
        unless owner != .null && other != .null && owner != other do
          throwError "counterexample lost the distinct module parameter bindings"
        -- Check the reconstructed Instantiation itself, not just raw solver JSON.
        liftTermElabM do
          let cti ← Veil.buildCounterexampleExprs model.raw mod revoke
          for (name, expected) in [(`CexComposition.Instantiation.owner, owner),
              (`CexComposition.Instantiation.other, other)] do
            let value ← mkAppM name #[cti.instExpr]
            let actual ← reconstructedNatJson value
            unless actual == expected do throwError "wrong reconstructed argument {name}: {actual}"
        let pre := json.getObjValD "preState"
        let before ← counterexampleNat (← counterexampleMapAt (← counterexampleField pre granted.toString) owner)
        let usedBefore ← counterexampleNat (← counterexampleField pre used.toString)
        unless 0 < before && usedBefore ≤ before do throwError "invalid revocation pre-state"
        let label := json.getObjValD "label"
        let .ok args := (label.getObjValD "args").getArr? | throwError "missing action arguments"
        unless label.getObjValD "name" == toJson revoke.toString &&
            args.size == 1 && args[0]!.getObjValD "value" == owner do
          throwError "counterexample action lost its owner argument"
        let post := json.getObjValD "postState"
        if post == .null then
          sawWP := true
        else
          sawTR := true
          let after ← counterexampleNat (← counterexampleMapAt (← counterexampleField post granted.toString) owner)
          let usedAfter ← counterexampleNat (← counterexampleField post used.toString)
          unless before == after + 1 && usedAfter == usedBefore && usedAfter > after do
            throwError "counterexample does not exhibit the foreign-step safety violation"
  unless sawWP && sawTR do throwError "expected structured WP and TR counterexamples"
end CexComposition

public class CexDictionary where
  amount : Nat
  deriving Repr

public instance : Inhabited CexDictionary := ⟨⟨99⟩⟩

veil module CexDictionaryParameters

param limit : Nat
type tenant
param owner : tenant
param dictionary : CexDictionary

individual used : Nat
individual holder : tenant

after_init { used := 0; holder := owner }

action spend (t : tenant) {
  require dictionary.amount > limit
  used := dictionary.amount
  holder := t
}

invariant [bounded] used ≤ limit
#gen_spec

#guard_msgs(drop info, drop warning) in
set_option veil.violationIsError false in
#check_invariants

run_cmd do
  let results ← Veil.Verifier.waitEnabledSync
  let mod ← Veil.getCurrentModule
  let mut count := 0
  for vc in results.vcs do
    let .induction metadata := vc.metadata | continue
    unless metadata.action == `spend && metadata.property == `bounded do continue
    for d in vc.timing.dischargers do
      let some (.disproven (some (.sat models)) _) := d.result | continue
      for model in models do
        let some model := model | throwError "missing structured dictionary counterexample"
        count := count + 1
        let json := model.structuredJson
        let extra := json.getObjValD "extraVals"
        let amount := if extra.getObjValD "dictionary" != .null then
          extra.getObjValD "dictionary" else extra.getObjValD "dictionary.amount"
        let limit ← counterexampleNat (extra.getObjValD "limit")
        unless (← counterexampleNat amount) > limit do throwError "lost the dictionary guard"
        liftTermElabM do
          let cti ← Veil.buildCounterexampleExprs model.raw mod `spend
          let dictionary ← mkAppM `CexDictionaryParameters.Instantiation.dictionary #[cti.instExpr]
          let field ← mkAppOptM ``CexDictionary.amount #[some dictionary]
          let actual ← reconstructedNatJson field
          unless actual == amount do throwError "dictionary was replaced by a default: {actual}"
          let limitExpr ← mkAppM `CexDictionaryParameters.Instantiation.limit #[cti.instExpr]
          let actualLimit ← reconstructedNatJson limitExpr
          unless actualLimit == toJson limit do throwError "wrong interleaved value parameter"
        let post := json.getObjValD "postState"
        if post != .null then
          unless (← counterexampleField post "used") == amount do
            throwError "post-state does not preserve the model dictionary value"
  unless count ≥ 2 do throwError "expected WP and TR dictionary counterexamples"

#guard_msgs(drop info, drop warning) in
sat trace {
  spend
  assert (used > limit)
}

run_cmd do
  let results ← Veil.Verifier.waitEnabledSync
  let mod ← Veil.getCurrentModule
  let mut found := false
  for vc in results.vcs do
    unless vc.metadata.isTrace do continue
    for d in vc.timing.dischargers do
      let some (.proven _ (some (.sat models)) _) := d.result | continue
      for model in models do
        let some model := model | throwError "missing structured symbolic trace"
        found := true
        let traceJson := model.structuredJson.getObjValD "trace"
        let extra := traceJson.getObjValD "extraVals"
        let amount := extra.getObjValD "dictionary.amount"
        let limit ← counterexampleNat (extra.getObjValD "limit")
        unless (← counterexampleNat amount) > limit do throwError "trace lost its value parameters"
        let .ok states := (traceJson.getObjValD "states").getArr? | throwError "missing trace states"
        unless states.size == 2 do throwError "wrong number of trace states"
        unless (← counterexampleField (states[0]!.getObjValD "fields") "used") == toJson (0 : Nat) &&
            (← counterexampleField (states[1]!.getObjValD "fields") "used") == amount do
          throwError "trace lost the dictionary-based state update"
        liftTermElabM do
          let sortMap ← Veil.parseSortsFromModel model.raw
          let (sorts, enums) ← Veil.resolveSortArgsAndEnumAdapts model.raw mod sortMap
          let (args, _) ← Veil.resolveModuleArgs model.raw mod sorts enums
          let inst ← Veil.buildInstantiationExpr mod args
          let dictionary ← mkAppM `CexDictionaryParameters.Instantiation.dictionary #[inst]
          let field ← mkAppOptM ``CexDictionary.amount #[some dictionary]
          let actual ← reconstructedNatJson field
          unless actual == amount do throwError "trace resynthesized its dictionary"
  unless found do throwError "expected a structured symbolic trace"

end CexDictionaryParameters
