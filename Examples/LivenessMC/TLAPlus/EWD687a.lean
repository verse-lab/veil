module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/ewd687a/EWD687a.tla
-- Dijkstra-Scholten termination detection for a diffusing computation (the "Tree Algorithm").
-- Instance and config: MCEWD687a.tla/.cfg.

veil module EWD687a

-- CONSTANTS Procs, Leader, Edges, and MCEWD687a's MaxCounter; src e = e[1] and dst e = e[2].
type proc
type edge
param Leader : proc
param src : edge → proc
param dst : edge → proc

param MaxCounter : Nat

-- Graphs!AreConnectedIn(n, Leader, O), for the overlay tree O of TreeWithRoot below.
param connectedToLeader : (proc → Option edge) → proc → Bool

-- VARIABLES active, sentUnacked, rcvdUnacked, upEdge, msgs, acks; NotAnEdge == << >> is `none`.
relation active : proc → Bool
function sentUnacked : edge → Nat
function rcvdUnacked : edge → Nat
function upEdge : proc → Option edge
function msgs : edge → Nat
function acks : edge → Nat

#gen_state

-- InEdges(p) == {e \in Edges : e[2] = p}
theory ghost relation InEdges (p : proc) (e : edge) := dst e = p

-- OutEdges(p) == {e \in Edges : e[1] = p}
theory ghost relation OutEdges (p : proc) (e : edge) := src e = p

-- ASSUME EdgeFacts == /\ \A e \in Edges : (e \in Procs \X Procs) /\ (e[1] # e[2])
--                     /\ Leader \in Procs /\ InEdges(Leader) = {}
assumption [EdgeFacts]
  (∀ e : edge, src e ≠ dst e) ∧ (∀ e : edge, ¬ InEdges Leader e)

-- `Edges` is a set of pairs, so two of its elements with the same endpoints are the same edge.
assumption [EdgesAreASet] ∀ e f : edge, src e = src f → dst e = dst f → e = f

-- neutral(p) == ~active[p] /\ (\A e \in InEdges(p) : rcvdUnacked[e] = 0)
--                          /\ (\A e \in OutEdges(p) : sentUnacked[e] = 0)
ghost relation neutral (p : proc) :=
  ¬ active p
  ∧ (∀ e : edge, InEdges p e → rcvdUnacked e = 0)
  ∧ (∀ e : edge, OutEdges p e → sentUnacked e = 0)

-- Init == /\ active = [p \in Procs |-> p = Leader] /\ upEdge = [p \in Procs \ {Leader} |-> NotAnEdge]
--         /\ msgs = acks = sentUnacked = rcvdUnacked = [e \in Edges |-> 0]
after_init {
  active P := decide (P = Leader)
  msgs E := 0
  acks E := 0
  sentUnacked E := 0
  rcvdUnacked E := 0
  upEdge P := none
}

-- SendMsg(p) == active[p] /\ \E e \in OutEdges(p) : sentUnacked' = [sentUnacked EXCEPT ![e] = @ + 1]
--                                                   /\ msgs' = [msgs EXCEPT ![e] = @ + 1]
action SendMsg (p : proc) {
  require active p
  let e :| OutEdges p e
  sentUnacked e := sentUnacked e + 1
  msgs e := msgs e + 1
}

-- RcvAck(p) == \E e \in OutEdges(p) : acks[e] > 0 /\ acks' = [acks EXCEPT ![e] = @ - 1]
--                                     /\ sentUnacked' = [sentUnacked EXCEPT ![e] = @ - 1]
action RcvAck (p : proc) {
  let e :| OutEdges p e ∧ acks e > 0
  assert sentUnacked e > 0
  acks e := acks e - 1
  sentUnacked e := sentUnacked e - 1
}

-- SendAck(p) == \E e \in InEdges(p) : rcvdUnacked[e] > 0 /\ ((e = upEdge[p]) => rcvdUnacked[e] > 1
--      \/ (~active[p] /\ (\A d \in InEdges(p) \ {e} : rcvdUnacked[d] = 0)
--                     /\ (\A d \in OutEdges(p) : sentUnacked[d] = 0)))
--   /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ - 1] /\ acks' = [acks EXCEPT ![e] = @ + 1]
action SendAck (p : proc) {
  let e :| InEdges p e ∧ rcvdUnacked e > 0
           ∧ (upEdge p = some e →
                rcvdUnacked e > 1
                ∨ (¬ active p
                   ∧ (∀ d : edge, InEdges p d → d ≠ e → rcvdUnacked d = 0)
                   ∧ (∀ d : edge, OutEdges p d → sentUnacked d = 0)))
  rcvdUnacked e := rcvdUnacked e - 1
  acks e := acks e + 1
  -- UP:: upEdge' = IF neutral(p)' THEN [upEdge EXCEPT ![p] = NotAnEdge] ELSE upEdge
  if neutral p then
    upEdge p := none
}

-- RcvMsg(p) == \E e \in InEdges(p) : msgs[e] > 0 /\ msgs' = [msgs EXCEPT ![e] = @ - 1]
--   /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ + 1] /\ active' = [active EXCEPT ![p] = TRUE]
--   /\ upEdge' = IF neutral(p) THEN [upEdge EXCEPT ![p] = e] ELSE upEdge
action RcvMsg (p : proc) {
  let e :| InEdges p e ∧ msgs e > 0
  if neutral p then
    upEdge p := some e
  msgs e := msgs e - 1
  rcvdUnacked e := rcvdUnacked e + 1
  active p := true
}

-- Idle(p) == active[p] /\ active' = [active EXCEPT ![p] = FALSE]
action Idle (p : proc) {
  require active p
  active p := false
}

-- Next == \E p \in Procs : SendMsg(p) \/ SendAck(p) \/ RcvMsg(p) \/ RcvAck(p) \/ Idle(p)

-- MCEWD687a: StateConstraint == \A e \in Edges : msgs[e] < MaxCounter /\ acks[e] < MaxCounter
--   /\ sentUnacked[e] < MaxCounter /\ rcvdUnacked[e] < MaxCounter
state_constraint [StateConstraint] ∀ e : edge,
  msgs e < MaxCounter ∧ acks e < MaxCounter
  ∧ sentUnacked e < MaxCounter ∧ rcvdUnacked e < MaxCounter

-- TypeOK == /\ active \in [Procs -> BOOLEAN] /\ msgs, acks, sentUnacked, rcvdUnacked \in [Edges -> Nat]
--           /\ upEdge \in [Procs \ {Leader} -> Edges \cup {NotAnEdge}]
--           /\ \A p \in Procs \ {Leader} : upEdge[p] # NotAnEdge => upEdge[p][2] = p
invariant [TypeOK]
  upEdge Leader = none
  ∧ ∀ p : proc, p ≠ Leader → ∀ e : edge, upEdge p = some e → dst e = p

-- CountersConsistent == \A e \in Edges : sentUnacked[e] = rcvdUnacked[e] + acks[e] + msgs[e]
invariant [CountersConsistent]
  ∀ e : edge, sentUnacked e = rcvdUnacked e + acks e + msgs e

-- E == {upEdge[p] : p \in DOMAIN upEdge} \ {NotAnEdge}
ghost relation overlayEdge (e : edge) := ∃ p : proc, upEdge p = some e

-- N == {e[2] : e \in E} \cup {Leader}
ghost relation overlayNode (n : proc) :=
  n = Leader ∨ ∃ e : edge, overlayEdge e ∧ dst e = n

-- TreeWithRoot == LET O == Transpose([edge |-> E, node |-> N]) IN IsTreeWithRoot(O, Leader) /\ N::
-- Not checked on TLC.
invariant [TreeWithRoot]
  -- IsDirectedGraph(O): O.edge \subseteq O.node \X O.node
  (∀ e : edge, overlayEdge e → overlayNode (dst e) ∧ overlayNode (src e))
  -- \A e \in O.edge : e[1] # Leader
  ∧ (∀ e : edge, overlayEdge e → dst e ≠ Leader)
  -- \A e \in O.edge : \A f \in O.edge : (e[1] = f[1]) => (e = f)
  ∧ (∀ e f : edge, overlayEdge e → overlayEdge f → dst e = dst f → src e = src f)
  -- \A n \in O.node : AreConnectedIn(n, Leader, O)
  ∧ (∀ n : proc, overlayNode n → connectedToLeader (fun p => upEdge p) n)
  -- N:: \A n \in O.node \ {Leader} : ~neutral(n)
  ∧ (∀ n : proc, overlayNode n → n ≠ Leader → ¬ neutral n)

-- DT1Inv == neutral(Leader) => \A p \in Procs \ {Leader} : neutral(p)
invariant [DT1Inv]
  neutral Leader → ∀ p : proc, p ≠ Leader → neutral p

-- Terminated == (\A p \in Procs : ~active[p]) /\ (\A e \in Edges : msgs[e] = 0)
ghost relation Terminated :=
  (∀ p : proc, ¬ active p) ∧ (∀ e : edge, msgs e = 0)

-- Spec == Init /\ [][Next]_vars /\ WF_vars(Next), where
--   WF_vars(Next) == []<>(<<Next>>_vars \/ ~ENABLED <<Next>>_vars)
-- DT2 == Terminated ~> neutral(Leader)
temporal (only := check) [DT2]
  (□ ◇ ((⟨SendMsg⟩ ∨ ⟨SendAck⟩ ∨ ⟨RcvMsg⟩ ∨ ⟨RcvAck⟩ ∨ ⟨Idle⟩)
        ∨ ¬ (Enabled SendMsg ∨ Enabled SendAck ∨ Enabled RcvMsg ∨ Enabled RcvAck ∨ Enabled Idle)))
  → (⌜ Terminated ⌝ ↝ ⌜ neutral Leader ⌝)

#gen_spec

-- MCProcs = {Leader, P1, P2, P3} as 0..3; MCEdges = {<<Leader,P1>>, <<P1,P2>>, <<P2,P1>>, <<P2,P3>>}.
abbrev NProcs : Nat := 4
abbrev NEdges : Nat := 4

def LeaderV : Fin NProcs := 0
def srcV : Fin NEdges → Fin NProcs := fun e => [0, 1, 2, 2].getD e.val 0
def dstV : Fin NEdges → Fin NProcs := fun e => [1, 2, 1, 3].getD e.val 0

-- O.edge == {<<e[2], e[1]>> : e \in E}, i.e. child/parent pairs.
def overlayEdgesV (u : Fin NProcs → Option (Fin NEdges)) : List (Fin NProcs × Fin NProcs) :=
  (List.finRange NProcs).filterMap (fun p => (u p).map (fun e => (dstV e, srcV e)))

def stepV (es : List (Fin NProcs × Fin NProcs)) (ns : List (Fin NProcs)) : List (Fin NProcs) :=
  ns ++ es.filterMap (fun cp => if ns.contains cp.1 then some cp.2 else none)

def connectedToLeaderV (u : Fin NProcs → Option (Fin NEdges)) (n : Fin NProcs) : Bool :=
  (Nat.repeat (stepV (overlayEdgesV u)) (NProcs - 1) [n]).contains LeaderV

-- MCEWD687a.cfg: MaxCounter = 3, Procs <- MCProcs, Edges <- MCEdges, CONSTRAINT StateConstraint,
--   CHECK_DEADLOCK FALSE (hence no `termination` clause), INVARIANTS TypeOK CountersConsistent
--   TreeWithRoot DT1Inv, PROPERTY DT2. TLC, with TreeWithRoot dropped: 18028 distinct states.
--#model_check compiled
--  { proc := Fin NProcs, edge := Fin NEdges, Leader := LeaderV, src := srcV, dst := dstV,
--    MaxCounter := 3, connectedToLeader := connectedToLeaderV } {}

--#temporal_check compiled
--  { proc := Fin NProcs, edge := Fin NEdges, Leader := LeaderV, src := srcV, dst := dstV,
--    MaxCounter := 3, connectedToLeader := connectedToLeaderV } {}

end EWD687a
