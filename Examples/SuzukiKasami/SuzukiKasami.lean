import Veil
import Veil.Core.Tools.Checker.Concrete.Main

-- https://github.com/markyuen/tlaplus-to-ivy/blob/main/ivy/suzuki_kasami.ivy

veil module SuzukiKasami


type node
type seq_t
immutable individual init_node : node

instantiate seq : TotalOrderWithMinimum seq_t

-- State

--- Nodes
function n_have_privilege : node → Bool
relation n_requesting : node → Bool
function n_RN : node → node → seq_t
-- the sequence number of the most recently granted request by `node`
function n_token_seq : node → seq_t

--- Requests
relation reqs : node → node → seq_t → Bool

--- Tokens
relation t_for : seq_t → node → Bool
function t_LN : seq_t → node → seq_t
relation t_q : seq_t → node → Bool

--- Critical section
relation crit : node → Bool

#gen_state

action succ (n : seq_t) {
  let k : seq_t ← pick
  assume seq.next n k;
  return k
}

after_init {
  n_have_privilege N := N == init_node;
  n_requesting N := false;
  n_RN N M := seq.zero;
  let one : seq_t ← succ seq.zero;
  n_token_seq N := if N = init_node then one else seq.zero;

  reqs N M I := false;

  t_for I N := decide $ (seq.next seq.zero I) ∧ N == init_node;
  t_LN I N := seq.zero;
  t_q I N := false;

  crit N := false
}

action request (n : node) {
  require ¬ n_requesting n;
  n_requesting n := true;
  if (¬ n_have_privilege n) then
    let k ← succ (n_RN n n)
    n_RN n n := k;
    reqs N n (n_RN n n) := decide $ N ≠ n
}

-- node `n` receiving a request from `m` with sequence number `r`
action rcv_request (n : node) (m : node) (r : seq_t) {
  require reqs n m r;
  n_RN n m := if seq.le r (n_RN n m) then n_RN n m else r;
  if (n_have_privilege n ∧ ¬ n_requesting n ∧ seq.next (t_LN (n_token_seq n) m) (n_RN n m)) then
    n_have_privilege n := false;
    let k : seq_t ← succ (n_token_seq n)
    t_for k m := true;
    t_LN k N := t_LN (n_token_seq n) N;
    t_q k N := t_q (n_token_seq n) N
}

action rcv_privilege (n: node) (t: seq_t) {
  require t_for t n;
  require seq.lt (n_token_seq n) t;
  n_have_privilege n := true;
  n_token_seq n := t
}

action enter (n : node) {
    require n_have_privilege n
    require n_requesting n
    -- Add n to crit
    crit n := true
}

action exit (n : node) {
  require crit n;
  crit n := false;
  n_requesting n := false;
  t_LN (n_token_seq n) n := n_RN n n;
  t_q (n_token_seq n) N := decide $ seq.next (t_LN (n_token_seq n) N) (n_RN n N);
  if m : (t_q (n_token_seq n) m) then
    t_q (n_token_seq n) m := false;
    n_have_privilege n := false;
    let k : seq_t ← succ (n_token_seq n)
    t_for k m := true;
    t_LN k N := t_LN (n_token_seq n) N;
    t_q k N := t_q (n_token_seq n) N
}

-- Invariants
invariant [mutex] (crit N ∧ crit M) → N = M
invariant [single_privilege] (n_have_privilege N ∧ n_have_privilege M) → N = M
invariant [allowed_in_crit] (crit N) → (n_have_privilege N ∧ n_requesting N)
invariant [unique_tokens] ((t_for I N) ∧ (t_for I M)) → N = M
invariant [corresponding_tokens] ((n_token_seq N) ≠ seq.zero) → t_for (n_token_seq N) N
invariant [current_privilege_latest_token_1] ((n_have_privilege N) ∧ N ≠ M) → seq.lt (n_token_seq M) (n_token_seq N)
invariant [current_privilege_latest_token_2] ((n_have_privilege N) ∧ (t_for I M)) → seq.le I (n_token_seq N)
-- invariant [current_privilege_latest_token_3] (∀ n, ¬ n_have_privilege n) → (∃ i m, t_for i m ∧ ∀ w, seq.lt (n_token_seq w) i)
-- invariant [current_privilege_latest_token_4] ((t_for I N) ∧ (∀ w, seq.lt (n_token_seq w) I)
--     ∧ (t_for J M) ∧ (∀ w, seq.lt (n_token_seq w) J))
--     → (I = J ∧ N = M)
invariant [no_request_to_self] (reqs N M I) → N ≠ M
invariant [no_consecutive_privilege] ((t_for I N) ∧ (seq.next J I) ∧ (t_for J M)) → N ≠ M
invariant [token_relation] ((t_for I N) ∧ (t_for J M) ∧ seq.lt I J) → seq.le I (n_token_seq N)

#gen_spec

-- #time #check_invariants

-- #gen_exec
deriving_FinOrdToJson_Domain
specify_FieldConcreteType
deriving_BEq_FieldConcreteType
deriving_Hashable_FieldConcreteType
deriving_rep_FieldRepresentation

deriving_lawful_FieldRepresentation


deriving_Inhabited_State
gen_NextAct
-- gen_executable_NextAct

end SuzukiKasami
