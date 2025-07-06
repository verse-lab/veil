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

def Label.gen2 : {quorum value seq_t replica_state replica : Type} →
  [Plausible.SampleableExt quorum] →
    [Plausible.SampleableExt value] →
      [Plausible.SampleableExt seq_t] →
        [Plausible.SampleableExt replica_state] →
          [Plausible.SampleableExt replica] → Plausible.Gen (Label quorum value seq_t replica_state replica) :=
fun {quorum value seq_t replica_state replica} [Plausible.SampleableExt quorum] [Plausible.SampleableExt value]
    [Plausible.SampleableExt seq_t] [Plausible.SampleableExt replica_state] [Plausible.SampleableExt replica] =>
  do
  let a ← Plausible.Gen.chooseAny (Fin 85)
  if a < 1 then pure Label.client_sends_request
  else if a < 40 then pure Label.handle_client_request
  else if a < 80 then pure Label.handle_marked_client_request_normal
  else
  match a with
    | ⟨80, isLt⟩ => do
      let __do_lift ← Plausible.SampleableExt.interpSample quorum
      let __do_lift_1 ← Plausible.SampleableExt.interpSample replica_state
      let __do_lift_2 ← Plausible.SampleableExt.interpSample seq_t
      pure (Label.handle_marked_client_drop_notification __do_lift __do_lift_1 __do_lift_2)
    | ⟨81, isLt⟩ => pure Label.handle_slot_lookup
    | ⟨82, isLt⟩ => pure Label.handle_gap_commit
    | ⟨83, isLt⟩ => pure Label.handle_gap_commit_rep
    | _ => pure Label.client_commit

-- to test if in the good case, a value from the client can be committed,
-- we (1) expose the nondeterminism in certain actions and (2) avoid the
-- "bad" choices that lead to the bad case
def Label.genGood (n : Nat) (r₀ : ⌞ Reader ⌟) : Plausible.Gen ⌞ Label ⌟ := do
  let l ← Label.gen2
  let good? : Bool := match l with
    | Label.handle_marked_client_drop_notification r _ _ => decide $ r ≠ r₀.leader
    | Label.handle_slot_lookup => false
    | _ => true
  if good? then return l
  match n with
  | 0 => pure l
  | n' + 1 => Label.genGood n' r₀

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
  @check_safety _ _ _ (sys := ⌞_ System _⌟) (Label.genGood 100 r₀) ⌞_ nextActExec _⌟ r₀ s₀ steps cfg
    (by intro r s; dsimp [invSimp]; infer_instance)

def randomizedCheck (steps : Nat) (cfg : Plausible.Configuration)
    : Plausible.Gen (RandomTrace ⌞ Reader ⌟ ⌞ State ⌟ ⌞ Label ⌟) := do
  let r₀ ← initReader
  let s₀ ← initState
  let s₀' := afterInit r₀ s₀
  checkCore r₀ s₀' steps cfg

#eval @randomizedCheck 2 1 3 1000 ({ } : Plausible.Configuration) |>.run 100

end NOPaxos
