module

public import Veil

/-!
Upstream license: MIT; see Benchmarks/TLA/Oswald/LICENSE.
Copyright (c) 2026 Jack Vanlightly
Modified locally: translated and adapted to Veil.

Safety translation of OSWALD at the source's selected Spec (without fairness).
Source (MIT):
https://github.com/Vanlightly/s3-wal-collection/blob/0a08df719f7512a85c15cd36b4dfdcc193e9ac0e/oswald/Oswald.tla
LSNs keep their source values. Chunk/snapshot objects remain partial maps;
machine data and pending data remain sequences. The set constant Values gives
WritableLsns = 0..Cardinality(Values), the fixed domain of auxObsSnapshots.
No symmetry, state projection, constraint, or deadlock check is selected.
-/

veil module Oswald

type writer
type gc
type value
type ValueSet
type LsnSet
type SnapshotSet
type ChunkMap
type SnapshotMap
type ObservationMap

enum WriterState = {snapshotRecovery, catchupRecovery, validate, ready, updateManifest}
enum GCState = {gcReady, gcDelete}

@[veil_decl]
structure Manifest where
  snapshotLsn : Nat
  gcWatermark : Nat
  version : Nat

instantiate values : TSet value ValueSet
instantiate lsns : TSet Nat LsnSet
instantiate observations : TSet (List value) SnapshotSet
instantiate chunks : TMap Nat value ChunkMap
instantiate snapshots : TMap Nat (List value) SnapshotMap
instantiate observed : TMap Nat SnapshotSet ObservationMap

immutable individual Values : ValueSet

individual manifest : Manifest
individual chunk : ChunkMap
individual snapshot : SnapshotMap
function wState : writer → WriterState
function wManifestVersion : writer → Nat
function wSafeLsn : writer → Nat
function wNextLsn : writer → Nat
function wMachineData : writer → List value
function wSnapshottedLsns : writer → LsnSet
function wPendingApply : writer → List value
function gcState : gc → GCState
function gcWm : gc → Nat
individual auxUsedValues : ValueSet
individual auxObsSnapshots : ObservationMap

set_option veil.deferVCGeneration true

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

assumption [values_complete] ∀ v : value, v ∈ Values

def SeqPrefixOf {α : Type} [BEq α] (s1 s2 : List α) : Bool :=
  s1.length ≤ s2.length && s2.take s1.length == s1

after_init {
  manifest := { snapshotLsn := 0, gcWatermark := 0, version := 0 }
  chunk := chunks.empty
  snapshot := snapshots.empty
  wState WW := snapshotRecovery
  wManifestVersion WW := 0
  wSafeLsn WW := 0
  wNextLsn WW := 1
  wMachineData WW := []
  wSnapshottedLsns WW := lsns.empty
  wPendingApply WW := []
  gcState G := gcReady
  gcWm G := 0
  auxUsedValues := values.empty
  auxObsSnapshots := (List.range (values.count Values + 1)).foldl
    (fun m lsn => observed.insert lsn observations.empty m) observed.empty
}

action SnapshotRecovery (w : writer) {
  require wState w = snapshotRecovery
  wManifestVersion w := manifest.version
  wSafeLsn w := manifest.snapshotLsn
  wNextLsn w := manifest.snapshotLsn + 1
  -- UpdateManifest follows WriteSnapshot; GC never deletes the current snapshot.
  -- Thus this default is unreachable when snapshotLsn > 0.
  wMachineData w := if manifest.snapshotLsn = 0 then [] else
    (snapshots.lookup manifest.snapshotLsn snapshot).getD []
  wPendingApply w := []
  wState w := catchupRecovery
}

action CatchupRecovery (w : writer) {
  require wState w = catchupRecovery
  let read := chunks.lookup (wNextLsn w) chunk
  if read.isSome then
    -- Some carries a real value; NIL is represented by none.
    wPendingApply w := wPendingApply w ++ read.toList
    wNextLsn w := wNextLsn w + 1
  else
    wState w := validate
}

-- auxObsSnapshots[lsn]; its domain stays WritableLsns.
ghost function ObservedAt (lsn : Nat) :=
  (observed.lookup lsn auxObsSnapshots).getD observations.empty

procedure ObserveSnapshot (w : writer) {
  let lsn := wNextLsn w - 1
  let snap := wMachineData w ++ wPendingApply w
  let previous := observed.lookup lsn auxObsSnapshots
  -- EXCEPT does not extend a function's domain. Reachable LSNs are in 0..|Values|.
  if previous.isSome then
    auxObsSnapshots := observed.insert lsn
      (observations.insert snap (previous.getD observations.empty)) auxObsSnapshots
}

action Validate (w : writer) {
  require wState w = validate
  if wManifestVersion w ≠ manifest.version ∧ wSafeLsn w ≤ manifest.gcWatermark then
    wState w := snapshotRecovery
    wPendingApply w := []
  else
    -- ObserveSnapshot reads the old machine/pending data, before they are replaced.
    ObserveSnapshot w
    wState w := ready
    wSafeLsn w := wNextLsn w
    wMachineData w := wMachineData w ++ wPendingApply w
    wPendingApply w := []
}

action AppendChunk (w : writer) (v : value) {
  require wState w = ready
  require wPendingApply w = []
  require v ∉ auxUsedValues
  if chunks.contains (wNextLsn w) chunk then
    wState w := catchupRecovery
  else
    chunk := chunks.insert (wNextLsn w) v chunk
    wNextLsn w := wNextLsn w + 1
    wPendingApply w := [v]
    wState w := validate
    auxUsedValues := values.insert v auxUsedValues
}

action WriteSnapshot (w : writer) {
  require wState w = ready
  require wPendingApply w = []
  require wNextLsn w > 1
  let lsn := wNextLsn w - 1
  require ¬ snapshots.contains lsn snapshot
  require lsn ∉ wSnapshottedLsns w
  snapshot := snapshots.insert lsn (wMachineData w) snapshot
  wState w := updateManifest
  wSnapshottedLsns w := lsns.insert lsn (wSnapshottedLsns w)
}

action UpdateManifest (w : writer) {
  require wState w = updateManifest
  let lsn := wNextLsn w - 1
  if manifest.snapshotLsn < lsn then
    manifest := { manifest with snapshotLsn := lsn, version := manifest.version + 1 }
  wState w := ready
}

action AdvanceGcWatermark (g : gc) {
  require gcState g = gcReady ∨ (gcState g = gcDelete ∧
    (¬ ∃ lsn ∈ chunks.keys chunk, lsn ≤ gcWm g) ∧
    (¬ ∃ lsn ∈ snapshots.keys snapshot, lsn ≤ gcWm g))
  require manifest.snapshotLsn ≠ manifest.gcWatermark
  let newWm := manifest.snapshotLsn
  manifest := { manifest with gcWatermark := newWm, version := manifest.version + 1 }
  gcState g := gcDelete
  gcWm g := newWm
}

action DeleteChunk (g : gc) {
  require gcState g = gcDelete
  let lsn : { l // l ∈ chunks.keys chunk } :| lsn.val ≤ gcWm g
  chunk := chunks.remove lsn.val chunk
}

action DeleteSnapshot (g : gc) {
  require gcState g = gcDelete
  let lsn : { l // l ∈ snapshots.keys snapshot } :| lsn.val < gcWm g
  snapshot := snapshots.remove lsn.val snapshot
}

-- Keep the semantic numeric bounds in TypeOK; the remaining conjuncts are typed.
invariant [TypeOK]
  (∀ lsn ∈ chunks.keys chunk, lsn ≤ values.count Values) ∧
  (∀ lsn ∈ snapshots.keys snapshot, lsn ≤ values.count Values) ∧
  ∀ w : writer, ∀ lsn : { l // l ∈ wSnapshottedLsns w }, lsn.val ≤ values.count Values

invariant [ConsistentWriterSnapshots]
  (∀ w : writer, wState w = ready →
    ((wMachineData w).length : Int) = (wNextLsn w : Int) - 1 ∧
    wMachineData w ∈ ObservedAt (wNextLsn w - 1)) ∧
  (∀ w1 w2 : writer, wState w1 = ready ∧ wState w2 = ready ∧
    wNextLsn w1 ≤ wNextLsn w2 → SeqPrefixOf (wMachineData w1) (wMachineData w2))

-- Binder types spell out ObservedAt: a state-reading ghost function there
-- breaks Veil's locality proof for the predicate.
invariant [ConsistentObservedSnapshots]
  (∀ lsn ≤ values.count Values, observations.count (ObservedAt lsn) ≤ 1) ∧
  (∀ lsn ≤ values.count Values,
    ∀ snap : { s : List value // s ∈ (observed.lookup lsn auxObsSnapshots).getD observations.empty },
      snap.val.length = lsn) ∧
  ∀ earlier ≤ values.count Values, ∀ later ≤ values.count Values, earlier ≤ later →
    ∀ earlierSnap : { s : List value //
        s ∈ (observed.lookup earlier auxObsSnapshots).getD observations.empty },
      ∀ laterSnap : { s : List value //
          s ∈ (observed.lookup later auxObsSnapshots).getD observations.empty },
        SeqPrefixOf earlierSnap.val laterSnap.val

#gen_spec
#gen_executable

/- EVAL
#model_check compiled
  { writer := Fin 2, gc := Fin 1, value := Fin 4,
    ValueSet := OrdList _,
    LsnSet := OrdList Nat, SnapshotSet := OrdList _,
    ChunkMap := Std.ExtTreeMap Nat _,
    SnapshotMap := Std.ExtTreeMap Nat _,
    ObservationMap := Std.ExtTreeMap Nat (OrdList _) }
  { Values := OrdList.ofList (List.finRange 4) }
  (seenSet := HAMTMapShard)
-/

-- -- Boundary: retain competing writers and GC, with one appendable value.
-- #model_check
--   { writer := Fin 2, gc := Fin 1, value := Fin 1, ValueSet := OrdList (Fin 1),
--     LsnSet := OrdList Nat, SnapshotSet := OrdList (List (Fin 1)),
--     ChunkMap := Std.ExtTreeMap Nat (Fin 1), SnapshotMap := Std.ExtTreeMap Nat (List (Fin 1)),
--     ObservationMap := Std.ExtTreeMap Nat (OrdList (List (Fin 1))) }
--   { Values := OrdList.ofList (List.finRange 1) } (fingerprintType := UInt64)

end Oswald
