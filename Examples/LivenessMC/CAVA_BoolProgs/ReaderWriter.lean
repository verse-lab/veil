import Veil

-- CAVA_LTL_Modelchecker/BoolProgs/Programs/BoolProgs_ReaderWriter.thy, `reader_writer` at
-- r=w=2 (matches `demo_rw_chosen = chose_prog (STR ''RW'') 2` in CAVA_Impl.thy). AFP entry:
-- https://www.isa-afp.org/entries/CAVA_LTL_Modelchecker.html. `readerStart`/`readersDone`
-- collapse CAVA's index-independent duplicate transitions (one copy per reader in
-- `reader_control`) into a single action each; per-index action comments are given once,
-- on the i=0 copies.
veil module BoolProgReaderWriter

individual ready : Bool
individual readersActive : Bool
individual writersActive : Bool
individual qError : Bool
individual activeR : Nat
individual reading0 : Bool
individual reading1 : Bool
individual writing0 : Bool
individual writing1 : Bool

#gen_state

after_init {
  ready := true
  readersActive := false
  writersActive := false
  qError := false
  activeR := 0
  reading0 := false
  reading1 := false
  writing0 := false
  writing1 := false
}

-- ready: ready,readers_active := FF,TT
action readerStart {
  require ready = true
  ready := false
  readersActive := true
}

-- readers_active ∧ ¬reading[i]: activeR++; reading[i] := TT
action readerInc0 {
  require readersActive = true ∧ reading0 = false
  activeR := activeR + 1
  reading0 := true
}

-- readers_active ∧ reading[i]: activeR--; reading[i] := FF
action readerDec0 {
  require readersActive = true ∧ reading0 = true
  activeR := activeR - 1
  reading0 := false
}

action readerInc1 {
  require readersActive = true ∧ reading1 = false
  activeR := activeR + 1
  reading1 := true
}

action readerDec1 {
  require readersActive = true ∧ reading1 = true
  activeR := activeR - 1
  reading1 := false
}

-- readers_active ∧ activeR=0: readers_active,ready := FF,TT
action readersDone {
  require readersActive = true ∧ activeR = 0
  readersActive := false
  ready := true
}

-- ready: ready,writers_active,writing[i] := FF,TT,TT
action writerStart0 {
  require ready = true
  ready := false
  writersActive := true
  writing0 := true
}

-- readers_active ∧ writing[i]: readers_active,q_error,writing[i] := FF,TT,FF
action writerErrorBranch0 {
  require readersActive = true ∧ writing0 = true
  readersActive := false
  qError := true
  writing0 := false
}

-- writers_active ∧ writing[i]: writers_active,ready,writing[i] := FF,TT,FF
action writerDone0 {
  require writersActive = true ∧ writing0 = true
  writersActive := false
  ready := true
  writing0 := false
}

action writerStart1 {
  require ready = true
  ready := false
  writersActive := true
  writing1 := true
}

action writerErrorBranch1 {
  require readersActive = true ∧ writing1 = true
  readersActive := false
  qError := true
  writing1 := false
}

action writerDone1 {
  require writersActive = true ∧ writing1 = true
  writersActive := false
  ready := true
  writing1 := false
}

safety [noQError] qError = false

-- Same property as the CAVA/Isabelle `demo_reader_writer` binary: G (not q_error).
liveness [φNoQError] □ ¬ ⌜ qError = true ⌝

-- Not checked in the corresponding Isabelle demo.
liveness [φWriterEventuallyActive] ◇ ⌜ writersActive = true ⌝

#gen_spec

#gen_executable

#eval Veil.LivenessMC.printCheckResult "BoolProgReaderWriter" "□(¬q_error)"
  (Veil.LivenessMC.check (enumerableTransitionSystem {})
    (φNoQError Theory (State FieldConcreteType) FieldConcreteType)
    (by native_decide) (by native_decide))

-- Not checked in Isabelle; left commented out, uncomment as a sanity check only.
/-
#eval Veil.LivenessMC.printCheckResult "BoolProgReaderWriter" "◇(writersActive)"
  (Veil.LivenessMC.check (enumerableTransitionSystem {})
    (φWriterEventuallyActive Theory (State FieldConcreteType) FieldConcreteType)
    (by native_decide) (by native_decide))
-/

end BoolProgReaderWriter
