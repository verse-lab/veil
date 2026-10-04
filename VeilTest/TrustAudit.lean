module

import Veil
import Veil.Core.Tools.LivenessMC.Benchmarking

meta section

/-! # What the shipped model-checking routes ask you to trust

`#print axioms` is **not** enough to answer "is this route verified?". It reports the axioms a proof
uses, and `@[implemented_by]` is a compiler directive, not an axiom: a route whose runtime behaviour
comes from hand-written `unsafe` code the kernel never checked still prints a clean
`[propext, Classical.choice, Quot.sound]`.

This file checks that it stays gone. It walks every constant reachable from each shipped route — through
types *and* values — and reports any that carries `@[implemented_by]` or is `unsafe`, ignoring Lean's own
core (`Array.foldlM → Array.foldlMUnsafe` and friends, which every Lean program has).

**The positive controls at the bottom are load-bearing.** Without them a passing run would be
indistinguishable from an audit that simply never finds anything. -/

open Lean

namespace VeilTest.TrustAudit

/-- Every constant reachable from `n`, through both its type and its value. -/
partial def collect (env : Environment) (seen : NameSet) (n : Name) : NameSet :=
  if seen.contains n then seen
  else
    let seen := seen.insert n
    match env.find? n with
    | none => seen
    | some ci =>
      let cs := ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[]
      cs.foldl (fun s c => collect env s c) seen

/-- Lean's own library, whose `@[implemented_by]` uses are part of the toolchain rather than of Veil. -/
def isCore (n : Name) : Bool :=
  [`Lean, `Array, `List, `Nat, `Std, `String, `UInt8, `UInt16, `UInt32, `UInt64, `USize, `IO,
   `ST, `EStateM, `Char, `Option, `Prod, `Subtype, `Substring, `System, `Float,
   `Int, `Fin, `BitVec, `ByteArray, `FloatArray].any (·.isPrefixOf n)

/-- `(non-core implemented_by, unsafe)` reachable from `roots`. -/
def scan (roots : List Name) : CoreM (Array (Name × Name) × Array Name) := do
  let env ← getEnv
  let seen := roots.foldl (fun s r => collect env s r) {}
  let mut impl : Array (Name × Name) := #[]
  let mut unsaf : Array Name := #[]
  for n in seen.toList do
    if !isCore n then
      if let some i := Lean.Compiler.getImplementedBy? env n then impl := impl.push (n, i)
      if let some ci := env.find? n then
        if ci.isUnsafe then unsaf := unsaf.push n
  return (impl, unsaf)

/-- A shipped route must reach no project-local `implemented_by` and no `unsafe`. -/
def mustBeClean (label : String) (roots : List Name) : CoreM Bool := do
  let (impl, unsaf) ← scan roots
  if impl.isEmpty && unsaf.isEmpty then
    IO.println s!"  ok    {label}"
    return true
  else
    IO.println s!"  FAIL  {label}: {impl.size} implemented_by, {unsaf.size} unsafe"
    for (n, i) in impl do IO.println s!"          {n} -> {i}"
    for n in unsaf do IO.println s!"          unsafe: {n}"
    return false

/-- A control must reach at least one, or this file is not testing anything. -/
def mustBeDirty (label : String) (roots : List Name) : CoreM Bool := do
  let (impl, unsaf) ← scan roots
  if impl.isEmpty && unsaf.isEmpty then
    IO.println s!"  FAIL  {label}: expected to find trusted code, found none -- the audit is vacuous"
    return false
  else
    IO.println s!"  ok    {label} (control: {impl.size} implemented_by)"
    return true

def run : CoreM Unit := do
  IO.println "TrustAudit: the six shipped routes, and two instrumented controls"
  let rs ← [
    mustBeClean "fair      Veil.LivenessMC.checkFair          " [``Veil.LivenessMC.checkFair],
    mustBeClean "prune     LTLLib.modelCheckFairFNFPruneOfStep" [``LTLLib.modelCheckFairFNFPruneOfStep],
    mustBeClean "patOnly   LTLLib.modelCheckFairDirectOfStep  " [``LTLLib.modelCheckFairDirectOfStep],
    mustBeClean "crossing  LTLLib.modelCheckFairFNFCrossOfStep" [``LTLLib.modelCheckFairFNFCrossOfStep],
    mustBeClean "dijkstra  LTLLib.modelCheckDijkstraOfStep    " [``LTLLib.modelCheckDijkstraOfStep],
    mustBeClean "ndfs      LTLLib.modelCheckNDFSOfStep        " [``LTLLib.modelCheckNDFSOfStep],
    mustBeDirty "CONTROL   Veil.LivenessMC.checkFairTimed     " [``Veil.LivenessMC.checkFairTimed],
    mustBeDirty "CONTROL   Veil.LivenessMC.checkDijkstraTimed " [``Veil.LivenessMC.checkDijkstraTimed]
  ].foldlM (fun acc m => do return acc.push (← m)) (#[] : Array Bool)
  IO.println (if rs.all id then "PASS" else "FAIL")
  if !rs.all id then throwError "TrustAudit failed"

end VeilTest.TrustAudit

-- Load private bodies too: ordinary module imports would make the audit stop at opaque definitions.
#eval show Lean.CoreM Unit from do
  let env ← Lean.importModules #[{ «module» := `Veil.Core.Tools.LivenessMC.Benchmarking }] {}
    (level := .private)
  Lean.withEnv env VeilTest.TrustAudit.run
