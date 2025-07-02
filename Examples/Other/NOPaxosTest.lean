import Examples.Other.NOPaxos

deriving_enum_instance_for NOPaxos.r_state

instance : FinEnum NOPaxos.r_state :=
  FinEnum.ofList
    [NOPaxos.r_state.st_normal, NOPaxos.r_state.st_gap_commit, NOPaxos.r_state.st_view_change]
    (by simp ; exact NOPaxos.r_state_Enum.r_state_complete)

open Plausible in
instance : SampleableExt NOPaxos.r_state where
  proxy := Fin 3
  sample := SampleableExt.interpSample (Fin 3)
  interp := fun x => match x.val with
    | 0 => NOPaxos.r_state.st_normal
    | 1 => NOPaxos.r_state.st_gap_commit
    | _ => NOPaxos.r_state.st_view_change

namespace NOPaxos

local instance (n : Nat) : DecidableRel (TotalOrderWithMinimum.le (t := Fin n.succ)) := by
  dsimp [TotalOrderWithMinimum.le] ; infer_instance

local instance (n : Nat) : DecidableRel (TotalOrderWithMinimum.lt (t := Fin n.succ)) := by
  dsimp [TotalOrderWithMinimum.lt] ; infer_instance

local instance (n : Nat) : DecidableRel (TotalOrderWithMinimum.next (t := Fin n.succ)) := by
  dsimp [TotalOrderWithMinimum.next] ; infer_instance

variable {n_replica n_value n_seq_t : Nat}

local macro "⌞ " t:term " ⌟" : term =>
  `(($t r_state (SimpleQuorum n_replica.succ) (Fin n_value.succ) (Fin n_seq_t.succ.succ) (Fin n_replica.succ)))

local macro "⌞_ " t:term " _⌟" : term =>
  `((⌞ $t ⌟ ⌞ State ⌟ ⌞ Reader ⌟))

def initReader : Plausible.Gen ⌞ Reader ⌟ := do
  let leader ← Plausible.SampleableExt.interpSample (Fin n_replica.succ)
  pure
    { one := ⟨1, Nat.succ_le_succ <| Nat.succ_le_succ <| Nat.zero_le _⟩
      lead := leader
      member := fun a b => a ∈ b.val
      leader := fun x => x = leader }

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

#eval @randomizedCheck 4 4 3 100 ({ } : Plausible.Configuration) |>.run 100

end NOPaxos
