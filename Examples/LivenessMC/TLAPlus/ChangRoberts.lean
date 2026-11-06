module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/chang_roberts/ChangRoberts.tla
-- Chang-Roberts leader election on a unidirectional ring: of the initiators, the one with the smallest identity wins.
-- From `MCChangRoberts.tla` + `MCChangRoberts.cfg`: `N = 3`, `Id == [i \in 1..N |-> i]`; `i : node` is TLA+ node `i + 1`.

veil module ChangRoberts

type node
param nodeId : node → Nat
-- succ(n) == IF n = N THEN 1 ELSE n+1
param succ : node → node

type IdSet
instantiate idSet : TSet Nat IdSet

enum PCLabel = {atN0, atN1, Done}
enum NodeState = {cand, lost, won}

function msgs : node → IdSet
function pc : node → PCLabel
relation initiator : node → Bool
function state : node → NodeState

#gen_state

-- ASSUME \A m,n \in Node : m # n => Id[m] # Id[n]
assumption [Id_unique] ∀ m n, m ≠ n → nodeId m ≠ nodeId n

-- Init == msgs = [n \in Node |-> {}] /\ initiator \in [Node -> BOOLEAN]
--         /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"] /\ pc = [self \in ProcSet |-> "n0"]
after_init {
  msgs X := idSet.empty
  initiator := *
  state X := if initiator X then cand else lost
  pc X := atN0
}

-- n0(self) == pc[self] = "n0" /\ IF initiator[self] THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}] ELSE msgs' = msgs
--             /\ pc' = [pc EXCEPT ![self] = "n1"] /\ UNCHANGED << initiator, state >>
action n0 (self : node) {
  require pc self = atN0
  if initiator self then
    msgs (succ self) := idSet.insert (nodeId self) (msgs (succ self))
  pc self := atN1
}

-- n1(self) == pc[self] = "n1" /\ pc' = [pc EXCEPT ![self] = "n1"] /\ UNCHANGED initiator /\ \E id \in msgs[self]:
--   LET _msgs == [msgs EXCEPT ![self] = @ \ {id}] IN IF state[self] = "lost" THEN msgs' = [_msgs EXCEPT ![succ(self)] = @ \cup {id}] /\ state' = state
--   ELSE IF id < Id[self] THEN state' = [state EXCEPT ![self] = "lost"] /\ msgs' = [_msgs EXCEPT ![succ(self)] = @ \cup {id}]
--   ELSE msgs' = _msgs /\ IF id = Id[self] THEN state' = [state EXCEPT ![self] = "won"] ELSE state' = state
action n1 (self : node) {
  require pc self = atN1
  let id ← pick { id // id ∈ msgs self }
  msgs self := idSet.remove id.val (msgs self)
  if state self = lost then
    msgs (succ self) := idSet.insert id.val (msgs (succ self))
  else
    if id.val < nodeId self then
      state self := lost
      msgs (succ self) := idSet.insert id.val (msgs (succ self))
    else
      if id.val = nodeId self then
        state self := won
  pc self := atN1
}

-- Terminating == (\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars
action Terminating {
  require ∀ self, pc self = Done
}

-- Next == (\E self \in Node: node(self)) \/ Terminating,  node(self) == n0(self) \/ n1(self)
-- No `\/ UNCHANGED vars` action: under this `Spec`'s fairness, stuttering is possible only at a dead end, where Veil stutters too.

-- TypeOK == pc \in [Node -> {"n0", "n1", "Done"}] /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
--           /\ initiator \in [Node -> BOOLEAN] /\ state \in [Node -> {"cand", "lost", "won"}]
invariant [TypeOK] ∀ n : node, ∀ id : { id // id ∈ msgs n }, ∃ m, nodeId m = id.val

-- Correctness == \A n \in Node : state[n] = "won" => initiator[n]
--                  /\ \A m \in Node \ {n} : state[m] = "lost" /\ (initiator[m] => Id[m] > Id[n])
invariant [Correctness] ∀ n, state n = won →
  initiator n ∧ ∀ m, m ≠ n → state m = lost ∧ (initiator m → nodeId m > nodeId n)

-- Liveness == (\E n \in Node : state[n] = "cand") => <>(\E n \in Node : state[n] = "won")
-- Spec == Init /\ [][Next]_vars /\ \A self \in Node : WF_vars(node(self))
temporal (only := check) [Liveness]
  (∀ self, (◇ □ (Enabled (n0 self) ∨ Enabled (n1 self))) → □ ◇ (⟨n0 self⟩ ∨ ⟨n1 self⟩)) →
    ⌜ ∃ n, state n = cand ⌝ → ◇ ⌜ ∃ n, state n = won ⌝

#gen_spec
#gen_executable

--#model_check
--  { node := Fin 3, IdSet := OrdList Nat, nodeId := fun i => i.val + 1, succ := fun i => i + 1 }

--#temporal_check
--  { node := Fin 3, IdSet := OrdList Nat, nodeId := fun i => i.val + 1, succ := fun i => i + 1 }

end ChangRoberts
