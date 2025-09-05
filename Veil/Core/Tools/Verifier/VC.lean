import Lean
open Lean Std

/-!
Data structures for representing and scheduling elaboration of theorems
in a dependency DAG, with support for equivalence classes of inter-derivable
theorems to avoid redundant SMT calls.

This module defines only the core data structures and basic helpers. The
execution engine (parallel scheduling, solver invocation, etc.) can be
built on top of these types.
-/

abbrev VCId := Nat

structure VCIdentifier where
  /-- A unique ID for this VC. -/
  uid : VCId
deriving Inhabited, BEq, Hashable

structure VCData (VCMetaT : Type) where
  /-- Name of this VC. If the VC gets proven, this will be the name of
  the `theorem` in the Lean environment. -/
  name : Name
  /-- Binders needed for the `statement` of the VC to make sense. -/
  params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  /-- The syntax of the statement (i.e. Lean type) of this VC. For
  convenience in generating `theorem` statements, we keep the binders
  separately, in the `params` field. -/
  statement : Term
  /-- Metadata associated with this VC, provided by the frontend. -/
  meta : VCMetaT
deriving Inhabited

structure VerificationCondition (VCMetaT : Type) extends VCIdentifier, (VCData VCMetaT)
deriving Inhabited

instance : BEq (VerificationCondition VCMetaT) where
  beq a b :=
    a.uid == b.uid &&
    a.statement == b.statement

instance : Hashable (VerificationCondition VCMetaT) where
  hash x := hash x.uid

def VerificationCondition.theoremStx [Monad m] [MonadQuotation m] (vc : VerificationCondition VCMetaT) : m Command := do
  `(command| theorem $(mkIdent vc.name) $(vc.params)* : $(vc.statement) := by sorry)

-- Based on [RustDagcuter](https://github.com/busyster996/RustDagcuter)
structure VCManager (VCMetaT : Type) where
  /-- All VCs, indexed by their ID. -/
  nodes : HashMap VCId (VerificationCondition VCMetaT)

  /-- Dependencies of each VC, i.e. VCs that must be proven before this
  VC can be proven. -/
  upstream : HashMap VCId (HashSet VCId)

  /-- In-degree count for each VC (number of upstream dependencies).
  Used for topological sorting: unfinished tasks with 0 in-degree
  should be executed next. -/
  inDegree : HashMap VCId Nat

  /-- Dependents of each VC, i.e. VCs that depend on _this_ VC. Used to
  update in-degrees when a task completes. -/
  downstream : HashMap VCId (HashSet VCId)

  protected _nextId : VCId := 0
deriving Inhabited

/--
  Adds a new verification condition (VC) to the VCManager, along with
  its upstream dependencies. Returns the updated VCManager and the new
  VC.
-/
def VCManager.addVC (mgr : VCManager VCMetaT) (vc : VCData VCMetaT) (dependsOn : HashSet VCId) : (VCManager VCMetaT × VCId) := Id.run do
  let uid := mgr._nextId
  let vc := { uid := uid, name := vc.name, params := vc.params, statement := vc.statement, meta := vc.meta }
  -- Add ourselves downstream of all our dependencies
  let mut downstream := mgr.downstream
  for parent in dependsOn do
    downstream := downstream.insert parent ((downstream[parent]? |>.getD {}).insert uid)
  let mgr' := { mgr with
    nodes := (mgr.nodes.insert uid vc),
    upstream := (mgr.upstream.insert uid dependsOn),
    inDegree := (mgr.inDegree.insert uid dependsOn.size),
    downstream := downstream,
    _nextId := mgr._nextId + 1
  }
  (mgr', uid)

instance [ToString VCMetaT] : ToString (VCManager VCMetaT) where
  toString mgr :=
    let nodes := mgr.nodes.toList.map (fun (uid, vc) => s!"[{uid}] {vc.name} depends on {mgr.upstream[uid]!.toList.map (fun dep => s!"{dep}")} (in-degree: {mgr.inDegree[uid]!}) {vc.meta}")
    s!"{String.intercalate "\n" nodes}"
