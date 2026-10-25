module

public import Veil

/-!
Upstream license: Apache-2.0; see Benchmarks/TLA/FileBasedLease/LICENSE.
Copyright 2023 DFINITY Foundation
Modified locally: translated and adapted to Veil.

Translation of the generated TLA+ actions in DFINITY's file-based lease model.
Source:
https://github.com/dfinity/formal-models/blob/09151cf5ea555afe62c5055b4188cfc54c7f98bf/tla/file_based_lease/Lease.tla
The selected relation is Next_With_Killing_And_Idling, including kill self-loops
and the explicit all-dead idle step. Option process represents ProcSet: some p
is a client and none is the distinct MARK_EXPIRED_ID. File IDs and idx use Int,
since Rename_Loop reaches -1. No fairness/liveness check is selected by Lease.cfg.
-/

veil module FileBasedLease

set_option veil.deferVCGeneration true

type process
type ProcessSet
type FileSet
instantiate processes : TSet process ProcessSet

enum PC = {Lease_Begin, Wait_For_Lock_0, Check_Stale, Wait_For_Stale,
  Wait_For_Lock_1, Wait_For_Stale_1, Rename_Loop, Release, Loop_Expiry, Done}

@[veil_decl]
structure File (process : Type) where
  id : Int
  pid : process
  expired : Bool

instantiate fileSet : TSet (File process) FileSet

function pc : Option process → PC
individual files : FileSet
function result_buffer : process → Bool
individual critical : ProcessSet
individual dead : ProcessSet
function idx : process → Int

veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

ghost relation Already_Exists (n : Int) :=
  ∃ f : { f // f ∈ files }, f.val.id = n

ghost relation Is_Expired (n : Int) :=
  ∃ f : { f // f ∈ files }, f.val.id = n ∧ f.val.expired

procedure Remove_File (id : Int) {
  files := fileSet.filter files (fun f => decide (f.id ≠ id))
}

-- Move's source CHOOSE has one witness on reachable states: unique file IDs,
-- and the live caller still owns its newly created idx+1 file.
procedure Move (fromId toId : Int) {
  let oldFiles := files
  let chosen : { f // f ∈ oldFiles } :| chosen.val.id = fromId
  let f := chosen.val
  files := fileSet.remove f files
  files := fileSet.filter files (fun other => decide (other.id ≠ toId))
  files := fileSet.insert { f with id := toId } files
}

after_init {
  files := fileSet.empty
  result_buffer P := false
  critical := processes.empty
  dead := processes.empty
  idx P := 0
  pc A := if A.isSome then Lease_Begin else Loop_Expiry
}

action LeaseBegin (p : process) {
  require pc (some p) = Lease_Begin
  if Already_Exists 0 then
    result_buffer p := false
  else
    files := fileSet.insert { id := 0, pid := p, expired := false } files
    result_buffer p := true
  pc (some p) := Wait_For_Lock_0
}

action WaitForLock0 (p : process) {
  require pc (some p) = Wait_For_Lock_0
  idx p := 0
  if result_buffer p then
    critical := processes.insert p critical
    pc (some p) := Release
  else
    pc (some p) := Check_Stale
}

action CheckStale (p : process) {
  require pc (some p) = Check_Stale
  result_buffer p := decide (Is_Expired (idx p))
  pc (some p) := Wait_For_Stale
}

action WaitForStale (p : process) {
  require pc (some p) = Wait_For_Stale
  if ¬ result_buffer p then
    pc (some p) := Lease_Begin
  else
    if Already_Exists (idx p + 1) then
      result_buffer p := false
    else
      files := fileSet.insert { id := idx p + 1, pid := p, expired := false } files
      result_buffer p := true
    pc (some p) := Wait_For_Lock_1
}

action WaitForLock1 (p : process) {
  require pc (some p) = Wait_For_Lock_1
  if ¬ result_buffer p then
    idx p := idx p + 1
    pc (some p) := Check_Stale
  else
    result_buffer p := decide (Is_Expired (idx p))
    pc (some p) := Wait_For_Stale_1
}

action WaitForStale1 (p : process) {
  require pc (some p) = Wait_For_Stale_1
  if ¬ result_buffer p then
    Remove_File (idx p + 1)
    pc (some p) := Lease_Begin
  else
    if idx p ≥ 0 then
      Move (idx p + 1) (idx p)
      -- The source reads files', after Move.
      result_buffer p := decide (Is_Expired (idx p))
      pc (some p) := Rename_Loop
    else
      Remove_File 0
      pc (some p) := Lease_Begin
}

action RenameLoop (p : process) {
  require pc (some p) = Rename_Loop
  idx p := idx p - 1
  -- The source reads idx'[p], not the old index.
  result_buffer p := decide (Is_Expired (idx p))
  pc (some p) := Wait_For_Stale_1
}

action ReleaseLease (p : process) {
  require pc (some p) = Release
  critical := processes.remove p critical
  Remove_File 0
  pc (some p) := Lease_Begin
}

action LoopExpiry {
  require pc none = Loop_Expiry
  let oldFiles := files
  let chosen : { f // f ∈ oldFiles } :| chosen.val.pid ∈ dead ∧ ¬ chosen.val.expired
  let f := chosen.val
  files := fileSet.remove f files
  files := fileSet.insert { f with expired := true } files
  pc none := Loop_Expiry
}

action Kill (p : process) {
  -- Source has no alive guard and does not clear the dead process's critical flag.
  pc (some p) := Done
  dead := processes.insert p dead
}

action Idle {
  require ∀ p : process, p ∈ dead
}

invariant [Only_One_Alive_Critical]
  processes.count (processes.diff critical dead) ≤ 1

invariant [No_Two_Files_With_Same_Id]
  ∀ f1 f2 : { f // f ∈ files }, f1.val.id = f2.val.id → f1.val = f2.val

-- Match TLC's enabled deadlock check. Kill means every state has a successor.
termination false

#gen_spec
#gen_executable

/- EVAL
#model_check compiled
  { process := Fin 5, ProcessSet := OrdList _,
    FileSet := OrdList _ } {}
      (seenSet := HAMTMapShard)
-/

-- Boundary: two clients still exercise stale-file reclamation and negative idx.
-- #model_check
--   { process := Fin 2, ProcessSet := OrdList (Fin 2),
--     FileSet := OrdList (File (Fin 2)) } {} (fingerprintType := UInt64)

end FileBasedLease
