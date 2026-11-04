module

public import Veil

-- https://github.com/tlaplus/Examples/blob/master/specifications/chang_roberts/ChangRoberts.tla
-- Chang-Roberts leader election on a unidirectional ring; N = 3 as in MCChangRoberts.cfg.

veil module ChangRoberts

type node
immutable function succ : node → node
immutable function Id : node → Nat
immutable individual n0 : node
immutable individual n1 : node
immutable individual n2 : node

enum St = { cand, lost, won }
function state : node → St
relation initiator : node → Bool
relation sent : node → Bool
relation msgPending : node → node → Bool -- msgPending r o : an id originating at `o` is waiting at `r`

#gen_state

assumption [id_injective] ∀ m n, m ≠ n → Id m ≠ Id n
assumption [ring0] succ n0 = n1
assumption [ring1] succ n1 = n2
assumption [ring2] succ n2 = n0

-- Init == initiator ∈ [Node -> BOOLEAN] /\ state = [self |-> IF initiator[self] THEN "cand" ELSE "lost"] /\ msgs = [n |-> {}]
after_init {
  let initV : node → Bool :| true
  initiator N := initV N
  state N := if initV N then cand else lost
  sent N := false
  msgPending R O := false
}

-- n0(self) == initiator[self] → msgs[succ(self)] += {Id[self]}
-- Split per node: `E`/`T` cannot name an instantiation, so the instantiation is baked into the
-- action and the label becomes nullary. `let self := nN` leaves the body verbatim. See the header.
action send_n0 {
  let self := n0
  require ¬ sent self
  if initiator self then
    msgPending (succ self) self := true
  sent self := true
}

action send_n1 {
  let self := n1
  require ¬ sent self
  if initiator self then
    msgPending (succ self) self := true
  sent self := true
}

action send_n2 {
  let self := n2
  require ¬ sent self
  if initiator self then
    msgPending (succ self) self := true
  sent self := true
}

-- n1(self) == \E id ∈ msgs[self]: (forward if lost or id < Id[self]; else consume, win if id = Id[self])
-- Split over both parameters, as `send` above: 9 nullary actions for the 3x3 instantiations.
action relay_n0_n0 {
  let self := n0
  let o := n0
  require sent self
  require msgPending self o
  if state self = lost then
    msgPending (succ self) o := true;
    msgPending self o := false
  else
    if Id o < Id self then
      state self := lost;
      msgPending (succ self) o := true;
      msgPending self o := false
    else
      msgPending self o := false;
      if o = self then
        state self := won
}

action relay_n0_n1 {
  let self := n0
  let o := n1
  require sent self
  require msgPending self o
  if state self = lost then
    msgPending (succ self) o := true;
    msgPending self o := false
  else
    if Id o < Id self then
      state self := lost;
      msgPending (succ self) o := true;
      msgPending self o := false
    else
      msgPending self o := false;
      if o = self then
        state self := won
}

action relay_n0_n2 {
  let self := n0
  let o := n2
  require sent self
  require msgPending self o
  if state self = lost then
    msgPending (succ self) o := true;
    msgPending self o := false
  else
    if Id o < Id self then
      state self := lost;
      msgPending (succ self) o := true;
      msgPending self o := false
    else
      msgPending self o := false;
      if o = self then
        state self := won
}

action relay_n1_n0 {
  let self := n1
  let o := n0
  require sent self
  require msgPending self o
  if state self = lost then
    msgPending (succ self) o := true;
    msgPending self o := false
  else
    if Id o < Id self then
      state self := lost;
      msgPending (succ self) o := true;
      msgPending self o := false
    else
      msgPending self o := false;
      if o = self then
        state self := won
}

action relay_n1_n1 {
  let self := n1
  let o := n1
  require sent self
  require msgPending self o
  if state self = lost then
    msgPending (succ self) o := true;
    msgPending self o := false
  else
    if Id o < Id self then
      state self := lost;
      msgPending (succ self) o := true;
      msgPending self o := false
    else
      msgPending self o := false;
      if o = self then
        state self := won
}

action relay_n1_n2 {
  let self := n1
  let o := n2
  require sent self
  require msgPending self o
  if state self = lost then
    msgPending (succ self) o := true;
    msgPending self o := false
  else
    if Id o < Id self then
      state self := lost;
      msgPending (succ self) o := true;
      msgPending self o := false
    else
      msgPending self o := false;
      if o = self then
        state self := won
}

action relay_n2_n0 {
  let self := n2
  let o := n0
  require sent self
  require msgPending self o
  if state self = lost then
    msgPending (succ self) o := true;
    msgPending self o := false
  else
    if Id o < Id self then
      state self := lost;
      msgPending (succ self) o := true;
      msgPending self o := false
    else
      msgPending self o := false;
      if o = self then
        state self := won
}

action relay_n2_n1 {
  let self := n2
  let o := n1
  require sent self
  require msgPending self o
  if state self = lost then
    msgPending (succ self) o := true;
    msgPending self o := false
  else
    if Id o < Id self then
      state self := lost;
      msgPending (succ self) o := true;
      msgPending self o := false
    else
      msgPending self o := false;
      if o = self then
        state self := won
}

action relay_n2_n2 {
  let self := n2
  let o := n2
  require sent self
  require msgPending self o
  if state self = lost then
    msgPending (succ self) o := true;
    msgPending self o := false
  else
    if Id o < Id self then
      state self := lost;
      msgPending (succ self) o := true;
      msgPending self o := false
    else
      msgPending self o := false;
      if o = self then
        state self := won
}

-- \/ UNCHANGED vars — models TLA+'s implicit stuttering steps under `[][Next]_vars`.
action stutter {
  pure ()
}

-- Correctness == a winner is the smallest-ID initiator, and everyone else has lost.
invariant [correctness] ∀ n, state n = won →
  initiator n ∧ ∀ m, m ≠ n → state m = lost ∧ (initiator m → Id m > Id n)

-- Not in the TLA+ source: `Liveness` is only ever checked against `Spec`, which bakes in
-- `\A self : WF_vars(node(self))`.
-- Not checked on TLC.
temporal [elect] (⌜ ∃ n, state n = cand ⌝) → ◇ ⌜ ∃ n, state n = won ⌝

-- Liveness == (∃n, state[n]=cand) ~> (∃n, state[n]=won), checked against Spec ==
-- Init /\ [][Next]_vars /\ ∀self : WF_vars(node(self)).
-- WF_v(node(self)) == □(◇¬E(node(self)) ∨ ◇T(node(self))), node(self) = send(self) ∨ relay(self,·).
-- No `□◇(¬T(stutter))` conjunct either: Spec has no WF_vars(Next), and per-process weak
-- fairness already rules out stuttering forever while anything is enabled.
temporal [electFair]
  ((□ (◇ ¬(E(send_n0) ∨ E(relay_n0_n0) ∨ E(relay_n0_n1) ∨ E(relay_n0_n2))
       ∨ ◇ (T(send_n0) ∨ T(relay_n0_n0) ∨ T(relay_n0_n1) ∨ T(relay_n0_n2))))
   ∧ (□ (◇ ¬(E(send_n1) ∨ E(relay_n1_n0) ∨ E(relay_n1_n1) ∨ E(relay_n1_n2))
       ∨ ◇ (T(send_n1) ∨ T(relay_n1_n0) ∨ T(relay_n1_n1) ∨ T(relay_n1_n2))))
   ∧ (□ (◇ ¬(E(send_n2) ∨ E(relay_n2_n0) ∨ E(relay_n2_n1) ∨ E(relay_n2_n2))
       ∨ ◇ (T(send_n2) ∨ T(relay_n2_n0) ∨ T(relay_n2_n1) ∨ T(relay_n2_n2)))))
  → ((⌜ ∃ n, state n = cand ⌝) → ◇ ⌜ ∃ n, state n = won ⌝)

#gen_spec

-- N=3 in MCChangRoberts.cfg. `Fin 3` node values 0,1,2 are the ring 0→1→2→0; `Id` is the identity.
def theory0 : Theory (Fin 3) St_IndT :=
  { succ := fun n => n + 1, Id := fun n => n.val, n0 := 0, n1 := 1, n2 := 2 }

#temporal_check [electFair] compiled { node := (Fin 3), St := St_IndT } theory0 (route := .fair)

end ChangRoberts
