module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/ewd687a/EWD687a.tla
-- Dijkstra-Scholten "Tree Algorithm" for termination detection. `Procs`/`Edges` fixed to
-- MCEWD687a.tla's graph (Leader, P1, P2, P3; edges L->P1, P1->P2, P2->P1, P2->P3).

veil module EWD687a

enum Proc = { L, P1, P2, P3 }
enum Edge = { E1, E2, E3, E4, NoEdge }

immutable function src : Edge → Proc
immutable function dst : Edge → Proc

relation active : Proc → Bool
function msgs : Edge → Nat
function acks : Edge → Nat
function sentUnacked : Edge → Nat
function rcvdUnacked : Edge → Nat
function upEdge : Proc → Edge

#gen_state

-- neutral(p) == ¬active[p] ∧ (∀e ∈ InEdges(p), rcvdUnacked[e]=0) ∧ (∀e ∈ OutEdges(p), sentUnacked[e]=0)
-- `NoEdge` is excluded throughout: it's a pure "no parent" sentinel (`src`/`dst NoEdge = L` only
-- so it typechecks), not a real edge, and must never be treated as one of L's in/out edges.
ghost relation neutral (p : Proc) :=
  ¬ active p ∧ (∀ e, e ≠ NoEdge → dst e = p → rcvdUnacked e = 0) ∧
    (∀ e, e ≠ NoEdge → src e = p → sentUnacked e = 0)

-- Init == active = [p |-> p = Leader] /\ msgs=acks=sentUnacked=rcvdUnacked = [e |-> 0]
--         /\ upEdge = [p \ {Leader} |-> NotAnEdge]
after_init {
  active P := decide $ P = L
  msgs E := 0
  acks E := 0
  sentUnacked E := 0
  rcvdUnacked E := 0
  upEdge P := NoEdge
}

-- SendMsg(p) == active[p] /\ ∃e ∈ OutEdges(p): sentUnacked'[e]=@+1 /\ msgs'[e]=@+1
action sendMsg (p : Proc) (e : Edge) {
  require active p
  require e ≠ NoEdge
  require src e = p
  -- MCEWD687a.cfg's MaxCounter = 3, as a precondition.
  require sentUnacked e < 2
  sentUnacked e := sentUnacked e + 1
  msgs e := msgs e + 1
}

-- RcvAck(p) == ∃e ∈ OutEdges(p): acks[e]>0 /\ acks'[e]=@-1 /\ sentUnacked'[e]=@-1
action rcvAck (p : Proc) (e : Edge) {
  require e ≠ NoEdge
  require src e = p
  require acks e > 0
  acks e := acks e - 1
  sentUnacked e := sentUnacked e - 1
}

-- SendAck(p) == ∃e ∈ InEdges(p): rcvdUnacked[e]>0 ∧ (e=upEdge[p] => rcvdUnacked[e]>1 ∨ neutral(p)')
--               ∧ rcvdUnacked'[e]=@-1 ∧ acks'[e]=@+1 ∧ UP: upEdge'[p] = NotAnEdge if neutral(p)' else upEdge[p]
action sendAck (p : Proc) (e : Edge) {
  require e ≠ NoEdge
  require dst e = p
  require rcvdUnacked e > 0
  require e = upEdge p →
    (rcvdUnacked e > 1 ∨
     (¬ active p ∧ (∀ d, d ≠ NoEdge → dst d = p ∧ d ≠ e → rcvdUnacked d = 0) ∧
        (∀ d, d ≠ NoEdge → src d = p → sentUnacked d = 0)))
  rcvdUnacked e := rcvdUnacked e - 1
  acks e := acks e + 1
  if neutral p then
    upEdge p := NoEdge
}

-- RcvMsg(p) == ∃e ∈ InEdges(p): msgs[e]>0 ∧ msgs'[e]=@-1 ∧ rcvdUnacked'[e]=@+1 ∧ active'[p]=TRUE
--              ∧ upEdge'[p] = e if neutral(p) else upEdge[p]
action rcvMsg (p : Proc) (e : Edge) {
  require e ≠ NoEdge
  require dst e = p
  require msgs e > 0
  let wasNeutral := neutral p
  msgs e := msgs e - 1
  rcvdUnacked e := rcvdUnacked e + 1
  active p := true
  if wasNeutral then
    upEdge p := e
}

-- Idle(p) == active[p] /\ active'[p] = FALSE
action idleAction (p : Proc) {
  require active p
  active p := false
}

-- \/ UNCHANGED vars — models TLA+'s implicit stuttering steps under `[][Next]_vars`.
action stutter {
  pure ()
}

-- CountersConsistent == ∀e ∈ Edges: sentUnacked[e] = rcvdUnacked[e] + acks[e] + msgs[e]
invariant [countersConsistent] ∀ e, e ≠ NoEdge → sentUnacked e = rcvdUnacked e + acks e + msgs e

-- DT1Inv == neutral(Leader) => ∀p ∈ Procs\{Leader}: neutral(p) — main safety property.
invariant [dt1Inv] neutral L → ∀ p, p ≠ L → neutral p

-- Terminated == (∀p, ¬active[p]) ∧ (∀e, msgs[e]=0). `~>` is `[](P => <>Q)`. Not in the TLA+
-- source: `DT2` is only ever checked against `Spec`, which bakes in WF_vars(Next).
-- Not checked on TLC.
temporal [dt2]
  □ (⌜ (∀ p, ¬ active p) ∧ (∀ e, e ≠ NoEdge → msgs e = 0) ⌝ → ◇ ⌜ neutral L ⌝)

-- DT2 == Terminated ~> neutral(Leader), checked against Spec == Init /\ [][Next]_vars /\ WF_vars(Next).
-- WF_vars(Next) == []<>(~ENABLED <<Next>>_vars \/ <<Next>>_vars). The `¬E(…)` disjunct is what makes
-- a run that terminates fair: after `Terminated` only acks are left, each of which shrinks the
-- outstanding counters, so every such run ends where `Next` is disabled. Without it (`□ ◇ ¬
-- T(stutter)` alone, an earlier version) no fair run ever reached `Terminated` and DT2 held
-- vacuously.
temporal [dt2Fair]
  (□ ◇ (¬ T(stutter) ∨ ¬ (E(sendMsg) ∨ E(rcvAck) ∨ E(sendAck) ∨ E(rcvMsg) ∨ E(idleAction)))) →
  □ (⌜ (∀ p, ¬ active p) ∧ (∀ e, e ≠ NoEdge → msgs e = 0) ⌝ → ◇ ⌜ neutral L ⌝)

#gen_spec

-- L→P1, P1→P2, P2→P1, P2→P3, matching MCEWD687a.tla's `MCEdges`.
def theory0 : Theory Proc_IndT Edge_IndT :=
  { src := fun e => if e = E1 then L else if e = E2 then P1 else if e = E3 then P2 else if e = E4 then P2 else L,
    dst := fun e => if e = E1 then P1 else if e = E2 then P2 else if e = E3 then P1 else if e = E4 then P3 else L }

#temporal_check [dt2Fair] compiled { Proc := Proc_IndT, Edge := Edge_IndT } theory0 (route := .fair)

end EWD687a
