import Examples.NOPaxos.NOPaxosExecutable

open Plausible in
instance : SampleableExt NOPaxos.replica_state where
  proxy := Bool
  sample := SampleableExt.interpSample Bool
  interp := fun x => if x then NOPaxos.replica_state.st_normal else NOPaxos.replica_state.st_gap_commit

namespace NOPaxos

local instance (n : Nat) : DecidableRel (TotalOrderWithZero.le (t := Fin n.succ)) := by
  dsimp [TotalOrderWithZero.le] ; infer_instance

local instance (n : Nat) : DecidableRel (lt (Fin n.succ)) := by infer_instance

local instance (n : Nat) : DecidableRel (next (Fin n.succ)) := by infer_instance

variable {n_replica n_value n_seq_t : Nat}

local macro "⌞ " t:term " ⌟" : term =>
  `(($t (Fin n_replica.succ) replica_state (Fin n_seq_t.succ.succ) (Fin n_value.succ) (SimpleQuorum n_replica.succ)))

local macro "⌞_ " t:term " _⌟" : term =>
  `((⌞ $t ⌟ ⌞ State ⌟ ⌞ Reader ⌟))

def initReader : Plausible.Gen ⌞ Reader ⌟ := do
  let leader ← Plausible.SampleableExt.interpSample (Fin n_replica.succ)
  pure
    { one := ⟨1, Nat.succ_le_succ <| Nat.succ_le_succ <| Nat.zero_le _⟩
      no_op := ⟨0, Nat.zero_lt_succ _⟩
      member := fun a b => a ∈ b.val
      leader := leader }

def initState : Plausible.Gen ⌞ State ⌟ := State.gen

def afterInit (r₀ : ⌞ Reader ⌟) (s₀ : ⌞ State ⌟) : ⌞ State ⌟ :=
  ⌞_ initExec _⌟ |>.run r₀ |>.run s₀
    |>.run |>.run |>.getD (Except.ok ((), default))
    |>.getD (fun _ => ((), default)) |>.snd

def checkCore (r₀ : ⌞ Reader ⌟) (s₀ : ⌞ State ⌟) (steps : Nat) (cfg : Plausible.Configuration)
    : Plausible.Gen (RandomTrace ⌞ Reader ⌟ ⌞ State ⌟ ⌞ Label ⌟) :=
  @check_safety _ _ _ (sys := ⌞_ System _⌟) Label.gen ⌞_ nextActExec _⌟ r₀ s₀ steps cfg
    (by intro r s; dsimp [invSimp]; infer_instance)

def randomizedCheck (steps : Nat) (cfg : Plausible.Configuration)
    : Plausible.Gen (RandomTrace ⌞ Reader ⌟ ⌞ State ⌟ ⌞ Label ⌟) := do
  let r₀ ← initReader
  let s₀ ← initState
  let s₀' := afterInit r₀ s₀
  checkCore r₀ s₀' steps cfg

#eval @randomizedCheck 2 1 3 500 ({ } : Plausible.Configuration) |>.run 100

end NOPaxos
