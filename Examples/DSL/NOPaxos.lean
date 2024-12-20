import Veil.State
import Veil.TransitionSystem
import Veil.Tactic
import Veil.DSL
-- https://github.com/markyuen/tlaplus-to-ivy/blob/main/ivy/nopaxos.ivy

section NOPaxos
open Classical

-- https://github.com/markyuen/tlaplus-to-ivy/blob/main/ivy/total_order.ivy
class TotalOrderWithMinimum (t : Type) :=
  -- relation: strict total order
  le (x y : t) : Prop
  -- axioms
  le_refl (x : t) : le x x
  le_trans (x y z : t) : le x y → le y z → le x z
  le_antisymm (x y : t) : le x y → le y x → x = y
  le_total (x y : t) : le x y ∨ le y x

  -- relation: nonstrict total order
  lt (x y : t) : Prop
  le_lt (x y : t) : lt x y ↔ (le x y ∧ x ≠ y)

  -- successor
  next (x y : t) : Prop
  next_def (x y : t) : next x y ↔ (lt x y ∧ ∀ z, lt x z → le z y)

  zero : t
  zero_lt (x : t) : le zero x


-- type r_state = { st_normal, st_gap_commit, st_view_change }
inductive r_state where
  | st_normal : r_state
  | st_gap_commit : r_state
  | st_view_change : r_state
type quorum
type value
type seq_t
type replica


-- Sequencer
relation s_seq_msg_num : seq_t → seq_t → Prop

-- Replica
relation r_log_len : replica → seq_t → Prop
relation r_log : replica → seq_t → value → Prop
relation r_sess_msg_num : replica → seq_t → Prop
relation r_gap_commit_reps : replica → replica → Prop
relation r_current_gap_slot : replica → seq_t → Prop
relation r_replica_status : replica → r_state → Prop

-- Network
relation m_client_request : value → Prop
relation m_marked_client_request : replica → value → seq_t → Prop
relation m_request_reply : replica → value → seq_t → Prop
relation m_slot_lookup : replica → replica → seq_t → Prop
relation m_gap_commit : replica → seq_t → Prop
relation m_gap_commit_rep : replica → replica → seq_t → Prop

-- Helpers
relation member : replica → quorum → Prop
relation leader : replica → Prop

individual no_op : value
individual one : seq_t
individual sequencer : seq_t
individual lead : replica

instantiate seq : TotalOrderWithMinimum seq_t

#gen_state NOPaxos

after_init {
    require seq.next seq.zero one; -- axiom [val_one]
    require ∀ (q₁: quorum) (q₂: quorum), ∃ (r: replica), member r q₁ ∧ member r q₂; -- axiom [quorum_intersection]
    require ∀ (R : replica), leader R ↔ R = lead; -- axiom [single_leader]
    fresh seq' : seq_t in
    fresh one' : seq_t in

    sequencer := seq';
    one := one';

    s_seq_msg_num S I := S = seq' ∧ I = one';

    r_log_len _ I := I = seq.zero;
    r_log _ _ _ := False;
    r_sess_msg_num _ S := S = one';
    r_gap_commit_reps _ _ := False;
    r_current_gap_slot _ I := I = seq.zero;
    r_replica_status _ S := S = r_state.st_normal;

    m_client_request _ := False;
    m_marked_client_request _ _ _ := False;
    m_request_reply _ _ _ := False;
    m_slot_lookup _ _ _ := False;
    m_gap_commit _ _ := False;
    m_gap_commit_rep _ _ _ := False
}

action _succ (n : seq_t) = {
    fresh k : seq_t in
    require seq.next k n;
    return k
}

-- Internal Actions
action replace_item (r : replica) (i : seq_t) (v : value) = {
    if len where (r_log_len r len) {
        k ← call !_succ len in
        if (seq.le i k) {
            r_log_len r I := I = i
        };
        r_log r i V := V = v
    }
}

action send_gap_commit (r : replica) = {
    if len where (r_log_len r len) {
        -- ensure leader r;
        -- ensure r_replica_status r r_state.st_normal;
        slot ← call !_succ len in
        r_replica_status r S := S = r_state.st_gap_commit;
        m_gap_commit r P := True;
        r_current_gap_slot r I := I = slot;
        m_gap_commit R slot := true
    }
}


 -- Exported Actions
action client_sends_request (v : value) = {
    require v ≠ no_op;
    m_client_request v := True
}

action handle_client_request (m_value : value) (s: seq_t) = {
    require s = sequencer;
    require m_client_request m_value;
    if slot where (s_seq_msg_num s slot) {
        m_marked_client_request R m_value slot := True;
        k ← call !_succ slot in
        s_seq_msg_num s I := I = k
    }
}

action handle_marked_client_request (r : replica) (m_value : value) (m_sess_msg_num : seq_t) = {
    require m_marked_client_request r m_value m_sess_msg_num;
    if len where (r_log_len r len) {
        if smn where (r_sess_msg_num r smn) {
            require r_replica_status r r_state.st_normal;
            if (m_sess_msg_num = smn) {
                r_log_len r I := I = smn;
                r_log r smn m_value := True;
                k ← call !_succ smn in
                r_sess_msg_num r I := I = k;
                m_request_reply r m_value smn := True
            };
            if (seq.lt smn m_sess_msg_num) {
                if (leader r) {
                    _ ← call !send_gap_commit r in skip
                } else {
                    m_slot_lookup lead r smn := True
                }
            }
        }
    }
}

action handle_slot_lookup (r : replica) (m_sender: replica) (m_sess_msg_num : seq_t) = {
    require m_slot_lookup r m_sender m_sess_msg_num;
    if len where (r_log_len r len) {
        require leader r;
        require r_replica_status r r_state.st_normal;
        if (seq.le m_sess_msg_num len) {
            if v where (r_log r m_sess_msg_num v) {
                m_marked_client_request m_sender v m_sess_msg_num := True
            } else {
                -- Nothing to undo
                skip
            }
        };
        k ← call !_succ len in
        if (m_sess_msg_num = k) {
            _ ← call !send_gap_commit r in skip
        }
    }
}

action handle_gap_commit (r: replica) (m_slot_num : seq_t) = {
    require m_gap_commit r m_slot_num;
    if len where (r_log_len r len) {
        if smn where (r_sess_msg_num r smn) {
            k ← call !_succ len in
            require seq.le m_slot_num k;
            require r_replica_status r r_state.st_normal ∨ r_replica_status r r_state.st_gap_commit;
            _ ← call !replace_item r m_slot_num no_op in skip;
            if (seq.lt len m_slot_num) {
                m ← call !_succ smn in
                r_sess_msg_num r I := I = m
            };
            m_gap_commit_rep lead r m_slot_num := True;
            m_request_reply r no_op m_slot_num := True
        }
    }
}

-- (*) Not part of the original protocol -- this is added simply to make writing
-- the inductive invariant easier. This condition always holds in an actual
-- execution before the replica status can be returned to normal. The reason
-- why is because for the recipient -- the leader -- to be part of the quorum,
-- it must have gone through the handle_gap_commit handler, incrementing its
-- sess msg num beyond the current gap slot. This condition is extracted to
-- this `before` construct simply for clarity -- there is no real operational
-- difference in this placement.

action handle_gap_commit_rep (r: replica) (m_sender : replica) (m_slot_num : seq_t) = {
    require r_sess_msg_num r I ∧ seq.lt m_slot_num I; -- *
    require m_gap_commit_rep r m_sender m_slot_num;
    require r_replica_status r r_state.st_gap_commit;
    require leader r;
    require r_current_gap_slot r m_slot_num;
    r_gap_commit_reps r m_sender := True;
    if (∃ (q: quorum), ∀ (p: replica), ((member r q) ∧ (member p q)
        → (r_gap_commit_reps r p))) {
        r_replica_status r S := S = r_state.st_normal
    }
}

invariant [sequencer_coherence] (s_seq_msg_num S I1 ∧ s_seq_msg_num S I2) → I1 = I2
invariant [ll_coherence] (r_log_len R I1 ∧ r_log_len R I2) → I1 = I2
invariant [log_coherence] (r_log R I V1 ∧ r_log R I V2) → V1 = V2
invariant [smn_coherence] (r_sess_msg_num R I1 ∧ r_sess_msg_num R I2) → I1 = I2
invariant [cgs_coherence] (r_current_gap_slot R I1 ∧ r_current_gap_slot R I2) → I1 = I2
invariant [status_coherence] (r_replica_status R S1 ∧ r_replica_status R S2) → S1 = S2

invariant [single_sequencer_1] (S = sequencer ∧ s_seq_msg_num sequencer I) → seq.le one I
invariant [single_sequencer_2] S ≠ sequencer → ¬ s_seq_msg_num S I

invariant [log_valid_1] (r_log R I V ∧ r_log_len R L) → seq.le I L
-- invariant [log_valid_2] (r_log_len R I ∧ seq.le J I) → ∃ v, r_log R J v -- (commented out in source)

invariant [leader_reply_matches_log] (leader R ∧ m_request_reply R V I) → r_log R I V

invariant [client_no_op] ¬ m_client_request no_op

invariant [marked_req_non_trivial] (V ≠ no_op ∧ m_marked_client_request R V I) → m_client_request V

invariant [request_reply_non_trivial] (V ≠ no_op ∧ m_request_reply R V I) → m_client_request V

invariant [log_non_trivial] (V ≠ no_op ∧ r_log R I V) → m_marked_client_request R V I

invariant [valid_sess_msg_num] (r_log_len R I ∧ r_sess_msg_num R J) → seq.next I J

invariant [lead_gap_commits] (leader R ∧ r_log_len R I ∧ seq.le J I) → (¬ m_gap_commit R J ∨ r_log R J no_op)

invariant [log_smn] (r_sess_msg_num R I ∧ seq.le I J) → ¬ r_log R J V

invariant [log_smn_gap] (leader R ∧ r_sess_msg_num R I ∧ seq.lt I J) → ¬ m_gap_commit R J

invariant [reply_smn] (m_request_reply R V I ∧ r_sess_msg_num R J) → seq.lt I J

invariant [leader_smn_gap] (leader R ∧ r_sess_msg_num R I ∧ m_gap_commit R I ∧ m_gap_commit R J ∧ seq.le J I)
    → (r_replica_status R r_state.st_gap_commit ∧ r_current_gap_slot R I)

safety [consistency] ((∃ (q: quorum), member lead q ∧ ∀ (r : replica), member r q → m_request_reply r V1 I) ∧
                (∃ (q: quorum), member lead q ∧ ∀ (r : replica), member r q → m_request_reply r V2 I))
                → V1 = V2

#gen_spec NOPaxos

-- #check_invariants
end NOPaxos
