module

public import VeilTest.ActionExecution
public meta import VeilTest.ActionExecution

/-!
TLA+ specs treat messages as untyped records: a handler picks a message, checks its kind (as in
`m.type = "reply"`), and then reads the fields of that kind (as in `m.view`). In Veil, the kinds
are constructors of one inductive type. Read directly, the fields need total accessors such as
`Msg.view` below, whose branches for the other kinds return a dummy value that is never used.
With `assume h : …` or `let m :| h : …`, a `match m, h with` (or an accessor taking `h`) lists
only the kind at hand: the proof `h` rules out the others.

Each `_total` action reads the fields through total accessors and is paired with a `_proof` action
that uses the proof instead; both must have the same executions.
-/

set_option linter.unusedVariables false

open VeilTest.ActionExecution

veil module ProofBindersMessages

@[veil_decl]
inductive Msg where
  | request (client : Nat) (value : Nat)
  | reply (replica : Nat) (view : Nat) (slot : Nat)

/- Total accessors: the second branch is never taken. -/
def Msg.view : Msg → Nat
  | .reply _ v _ => v
  | _ => 0

def Msg.slot : Msg → Nat
  | .reply _ _ s => s
  | _ => 0

def Msg.newerReply (lv : Nat) : Msg → Bool
  | .reply _ v _ => decide (v ≥ lv)
  | _ => false

/- With the proof, the accessor has no other branch. -/
def Msg.viewOfNewerReply : (m : Msg) → (lv : Nat) → m.newerReply lv = true → Nat
  | .reply _ v _, _, _ => v

individual messages : List Msg
individual lastView : Nat
individual lastSlot : Nat

#gen_state

after_init {
  messages := [.request 1 5, .reply 2 3 4]
  lastView := 0
  lastSlot := 0
}

/- The kind is assumed, then each field is read by a total accessor. -/
action receive_reply_total {
  let m :| m ∈ messages
  assume m matches .reply ..
  lastView := m.view
  lastSlot := m.slot
}

action receive_reply_proof {
  let m :| m ∈ messages
  assume h : m matches .reply ..
  let (v, s) := match m, h with
    | .reply _ v s, _ => (v, s)
  lastView := v
  lastSlot := s
}

action newer_reply_total {
  let m : {m // m ∈ messages} :| (match m.val with
    | .reply _ v _ => decide (v ≥ lastView)
    | _ => false) = true
  let v := match m.val with
    | .reply _ v _ => v
    | _ => 0
  lastView := v
}

action newer_reply_proof {
  let lv := lastView
  let m : {m // m ∈ messages} :| h : m.val.newerReply lv = true
  lastView := m.val.viewOfNewerReply lv h
}

def mixed : State FieldConcreteType :=
  { messages := [.request 1 5, .reply 2 3 4], lastView := 0, lastSlot := 0 }
def twoReplies : State FieldConcreteType :=
  { messages := [.reply 2 3 4, .reply 7 1 9], lastView := 2, lastSlot := 0 }
def requestsOnly : State FieldConcreteType :=
  { messages := [.request 1 5], lastView := 0, lastSlot := 0 }

#guard exactlyOneSuccess (__veil_exec_action% {} {} mixed receive_reply_proof) fun _ s =>
  s.lastView == 3 && s.lastSlot == 4
#guard exactlyNSuccesses 2 (__veil_exec_action% {} {} twoReplies receive_reply_proof) fun _ _ => true
#guard hasNoExecutions (__veil_exec_action% {} {} requestsOnly receive_reply_proof)

#guard exactlyOneSuccess (__veil_exec_action% {} {} mixed newer_reply_proof) fun _ s => s.lastView == 3
#guard exactlyOneSuccess (__veil_exec_action% {} {} twoReplies newer_reply_proof) fun _ s =>
  s.lastView == 3
#guard hasNoExecutions (__veil_exec_action% {} {} requestsOnly newer_reply_proof)

#guard [mixed, twoReplies, requestsOnly].all fun st =>
  __veil_exec_action% {} {} st receive_reply_total == __veil_exec_action% {} {} st receive_reply_proof
#guard [mixed, twoReplies, requestsOnly].all fun st =>
  __veil_exec_action% {} {} st newer_reply_total == __veil_exec_action% {} {} st newer_reply_proof

invariant [view_bounded] lastView ≤ 3

#gen_spec

/-- info: ✅ No violation (explored 3 states) -/
#guard_msgs in
#model_check interpreted { } { }

end ProofBindersMessages
