import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Backend.SMT.Result

/-!
# Verification Condition Metadata

This module defines metadata types for verification conditions. There are two
distinct kinds of VCs:

1. **Induction VCs** - Check that propositions are inductive (invariant preservation)
2. **Trace VCs** - Check symbolic trace containment (sat/unsat queries)

These are represented as a sum type `VCMetadata` to allow a single VCManager
to handle both.
-/

open Lean

namespace Veil

/-- The proof style used for a VC. -/
inductive VCStyle where
  /-- Weakest precondition style: uses VeilM semantics. -/
  | wp
  /-- Transition style: uses Transition semantics. -/
  | tr
deriving Inhabited, BEq, Hashable

instance : ToString VCStyle where
  toString style :=
    match style with
    | .wp => "wp"
    | .tr => "tr"

instance : ToJson VCStyle where
  toJson style :=
    match style with
    | .wp => "wp"
    | .tr => "tr"

instance : FromJson VCStyle where
  fromJson? json := do
    let s ← fromJson? json
    match s with
    | "wp" => pure .wp
    | "tr" => pure .tr
    | _ => .error s!"Invalid VCStyle: {s}"

/-! ## Induction VC Metadata -/

/-- VC kinds for inductive verification only. -/
inductive InductionVCKind where
  /-- Primary VCs are those that are _needed_ to derive other VCs. We
  try to prove these by SMT, if possible. -/
  | primary
  /-- Derived VCs typically do not require proof by SMT — they rely on
  applications of primary VCs (and potentially other derived VCs). -/
  | derived
  /-- Alternative VCs are associated with a primary VC and only run
  when all dischargers of the primary VC fail. -/
  | alternative
deriving Inhabited, BEq, Hashable

instance : ToString InductionVCKind where
  toString kind :=
    match kind with
    | .primary => "primary"
    | .derived => "derived"
    | .alternative => "alternative"

instance : ToJson InductionVCKind where
  toJson kind :=
    match kind with
    | .primary => "primary"
    | .derived => "derived"
    | .alternative => "alternative"

instance : FromJson InductionVCKind where
  fromJson? json := do
    let s ← fromJson? json
    match s with
    | "primary" => pure .primary
    | "derived" => pure .derived
    | "alternative" => pure .alternative
    | _ => .error s!"Invalid InductionVCKind: {s}"

/-- Metadata for inductive verification conditions (invariant preservation). -/
structure InductionVCMetadata where
  /-- The kind of this VC (primary, derived, alternative). -/
  kind : InductionVCKind
  /-- The proof style used for this VC (WP or TR). -/
  style : VCStyle
  /-- The action that this VC is about. -/
  action : Name
  /-- The property that this VC is about. -/
  property : Name
  /-- Module parameters for the VC statement. -/
  baseParams : Array Parameter
  /-- Extra parameters for the VC statement. -/
  extraParams : Array Parameter
  /-- The declarations that this VC's _statement_ depends on. The proof
  might need additional dependencies. -/
  stmtDerivedFrom : Std.HashSet Name
deriving Inhabited

instance : ToString InductionVCMetadata where
  toString m := s!"({m.kind}: {m.action}.{m.property})"

instance : ToJson InductionVCMetadata where
  toJson m :=
    Json.mkObj [
      ("kind", toJson m.kind),
      ("style", toJson m.style),
      ("action", toJson m.action),
      ("property", toJson m.property),
    ]

instance : FromJson InductionVCMetadata where
  fromJson? json := do
    let kind ← json.getObjValAs? InductionVCKind "kind"
    let style ← json.getObjValAs? VCStyle "style"
    let action ← json.getObjValAs? Name "action"
    let property ← json.getObjValAs? Name "property"
    pure {
      kind := kind
      style := style
      action := action
      property := property
      baseParams := #[]
      extraParams := #[]
      stmtDerivedFrom := ∅
    }

/-! ## Trace VC Metadata -/

/-- Metadata for trace verification conditions (symbolic model checking). -/
structure TraceVCMetadata where
  /-- Whether SAT is the expected result (true for `sat trace`, false for `unsat trace`). -/
  isExpectedSat : Bool
  /-- Number of transitions in the trace. -/
  numTransitions : Nat
  /-- Optional user-provided trace name. -/
  traceName : Option Name := none
deriving Inhabited

instance : ToString TraceVCMetadata where
  toString m :=
    let kind := if m.isExpectedSat then "sat" else "unsat"
    match m.traceName with
    | some n => s!"({kind} trace [{n}], {m.numTransitions} transitions)"
    | none => s!"({kind} trace, {m.numTransitions} transitions)"

instance : ToJson TraceVCMetadata where
  toJson m :=
    Json.mkObj [
      ("isExpectedSat", toJson m.isExpectedSat),
      ("numTransitions", toJson m.numTransitions),
      ("traceName", toJson m.traceName),
    ]

instance : FromJson TraceVCMetadata where
  fromJson? json := do
    let isExpectedSat ← json.getObjValAs? Bool "isExpectedSat"
    let numTransitions ← json.getObjValAs? Nat "numTransitions"
    let traceName ← json.getObjValAs? (Option Name) "traceName"
    pure { isExpectedSat, numTransitions, traceName }

/-! ## Unified VC Metadata -/

/-- Unified VC metadata type for VCManager.

This is a sum type that represents either an induction VC (for invariant
preservation checking) or a trace VC (for symbolic model checking). -/
inductive VCMetadata where
  /-- Induction VC for invariant preservation checking. -/
  | induction : InductionVCMetadata → VCMetadata
  /-- Trace VC for symbolic model checking. -/
  | trace : TraceVCMetadata → VCMetadata
deriving Inhabited

instance : ToString VCMetadata where
  toString
  | .induction m => toString m
  | .trace m => toString m

instance : ToJson VCMetadata where
  toJson
  | .induction m => Json.mkObj [("type", "induction"), ("data", toJson m)]
  | .trace m => Json.mkObj [("type", "trace"), ("data", toJson m)]

instance : FromJson VCMetadata where
  fromJson? json := do
    let type ← json.getObjValAs? String "type"
    let data ← json.getObjVal? "data"
    match type with
    | "induction" => return .induction (← FromJson.fromJson? data)
    | "trace" => return .trace (← FromJson.fromJson? data)
    | _ => .error s!"Unknown VCMetadata type: {type}"

/-! ## Helper Accessors -/

/-- Get the action name for display purposes. Returns `none` for trace VCs. -/
def VCMetadata.actionName? : VCMetadata → Option Name
  | .induction m => some m.action
  | .trace _ => none

/-- Get the property name for display purposes. Returns trace name for trace VCs. -/
def VCMetadata.propertyName? : VCMetadata → Option Name
  | .induction m => some m.property
  | .trace m => m.traceName

/-- Get a display name for the VC. -/
def VCMetadata.displayName : VCMetadata → String
  | .induction m => s!"{m.action}.{m.property}"
  | .trace m =>
    let kind := if m.isExpectedSat then "sat" else "unsat"
    match m.traceName with
    | some n => s!"{kind} trace [{n}]"
    | none => s!"{kind} trace"

/-- Get the kind string for display purposes. -/
def VCMetadata.kindString : VCMetadata → String
  | .induction m => toString m.kind
  | .trace _ => "trace"

/-- Check if this is an induction VC. -/
def VCMetadata.isInduction : VCMetadata → Bool
  | .induction _ => true
  | .trace _ => false

/-- Check if this is a trace VC. -/
def VCMetadata.isTrace : VCMetadata → Bool
  | .induction _ => false
  | .trace _ => true

end Veil
