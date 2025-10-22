-- import Veil
-- import Veil.Frontend.DSL.Action.Extraction.Extract
-- /-
--   This is a simplified version of the NOPaxos protocol, without view
--   changes. As such, the leader is modelled as fixed.
-- -/
-- veil module NOPaxos

-- type replica

-- -- Network
-- relation m_client_request (v : replica)
-- relation m_marked_client_request  (dest : replica) (v : replica) (sess_msg_num : replica)
-- relation m_request_reply (sender : replica) (request : replica) (log_slot_num : replica)
-- relation m_slot_lookup (dest : replica) (sender : replica) (sess_msg_num : replica)
-- relation m_gap_commit (dest : replica) (slot_num : replica)
-- relation m_gap_commit_rep (dest : replica) (sender : replica) (slot_num : replica)

-- -- Ghost state
-- relation gh_r_received_sequenced_client_request (r : replica) (s : replica)
-- relation gh_r_received_drop_notification (r : replica) (s : replica)
-- relation gh_committed (s : replica) (v : replica)

-- #gen_state


-- after_init {
--   m_client_request V := false
--   m_marked_client_request D V SMN := false

--   -- m_client_request V := false
--   -- m_marked_client_request D V SMN := false
--   -- m_request_reply S V LSN := false
--   -- m_slot_lookup D S SMN := false
--   -- m_gap_commit D SN := false
--   -- m_gap_commit_rep D S SN := false

--   gh_r_received_sequenced_client_request R S := false
--   gh_r_received_drop_notification R S := false
--   gh_committed S V := false
-- }

-- set_option maxHeartbeats 10000000
-- #time #gen_spec

-- -- #time #check_invariants

-- open Lean Meta Elab Command Veil in
-- scoped elab "⌞? " t:term " ⌟" : term => do
--   let lenv ← localEnv.get
--   let some mod := lenv.currentModule | throwError s!"Not in a module"
--   Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

-- -- #time #check_invariants
-- section

-- veil_variables

-- omit χ χ_rep χ_rep_lawful

-- open Veil Extract

-- variable [FinEnum replica] [Hashable replica]

-- def instFinEnumForComponents (f : State.Label)
--   : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     infer_instance_for_iterated_prod

-- instance instDecidableEqForComponents'' (f : State.Label)
--   : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', State.Label.toDomain] <;>
--     infer_instance

-- instance instHashableForComponents' (f : State.Label)
--   : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd', State.Label.toDomain] <;>
--     infer_instance

-- abbrev FieldConcreteType (f : State.Label) : Type :=
--   match f with
--   | State.Label.m_client_request => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_client_request)
--   | State.Label.m_marked_client_request => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_marked_client_request)
--   | State.Label.m_request_reply => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_request_reply)
--   | State.Label.m_slot_lookup => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_slot_lookup)
--   | State.Label.m_gap_commit  => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_gap_commit)
--   | State.Label.m_gap_commit_rep => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_gap_commit_rep)
--   | State.Label.gh_r_received_sequenced_client_request => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.gh_r_received_sequenced_client_request)
--   | State.Label.gh_r_received_drop_notification => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.gh_r_received_drop_notification)
--   | State.Label.gh_committed => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.gh_committed)

-- instance instReprForComponents  [Repr replica]
--   -- [Repr replica_state] [Repr value] [Repr quorum] [Repr seq_t]
--   (f : State.Label)
--   : Repr ((⌞? FieldConcreteType ⌟) f) := by
--   cases f <;>
--     dsimp only [IteratedProd, IteratedProd', List.foldr, FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] <;>
--     infer_instance

-- instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
--   constructor ; constructor <;>
--   dsimp only [FieldConcreteType, State.Label.toCodomain] <;>
--   exact default

-- instance rep (f : State.Label) : FieldRepresentation
--   ((⌞? State.Label.toDomain ⌟) f)
--   ((⌞? State.Label.toCodomain ⌟) f)
--   ((⌞? FieldConcreteType ⌟) f) := -- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
--   match f with
--     | State.Label.m_client_request =>
--       instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_client_request)
--     | State.Label.m_marked_client_request =>
--       instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_marked_client_request)
--     | State.Label.m_request_reply =>
--       instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_request_reply)
--     | State.Label.m_slot_lookup =>
--       instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_slot_lookup)
--     | State.Label.m_gap_commit =>
--       instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit)
--     | State.Label.m_gap_commit_rep =>
--       instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit_rep)
--     | State.Label.gh_r_received_sequenced_client_request =>
--       instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_sequenced_client_request)
--     | State.Label.gh_r_received_drop_notification =>
--       instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_drop_notification)
--     | State.Label.gh_committed =>
--       instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_committed)

-- #check  FinsetLike

-- instance lawful (f : State.Label) : LawfulFieldRepresentation
--   ((⌞? State.Label.toDomain ⌟) f)
--   ((⌞? State.Label.toCodomain ⌟) f)
--   ((⌞? FieldConcreteType ⌟) f)
--   ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
--   match f with
--     | State.Label.m_client_request =>
--       instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_client_request)
--     | State.Label.m_marked_client_request =>
--       instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_marked_client_request)
--     | State.Label.m_request_reply =>
--       instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_request_reply)
--     | State.Label.m_slot_lookup =>
--       instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_slot_lookup)
--     | State.Label.m_gap_commit =>
--       instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit)
--     | State.Label.m_gap_commit_rep =>
--       instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit_rep)
--     | State.Label.gh_r_received_sequenced_client_request =>
--       instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_sequenced_client_request)
--     | State.Label.gh_r_received_drop_notification =>
--       instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_drop_notification)
--     | State.Label.gh_committed =>
--       instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_committed)
-- end


-- attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
--   instFinEnumForComponents in
-- -- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
-- #specialize_nextact with FieldConcreteType
--   injection_begin
--     [FinEnum replica] [Hashable replica]
--   injection_end => NextAct'

-- #gen_executable_list! log_entry_being Std.Format
--   targeting NextAct'
--   injection_begin
--     [FinEnum replica] [Hashable replica]
--   injection_end

-- #check initMultiExec
-- #check nextActMultiExec

-- simple_deriving_repr_for' State
-- deriving instance Repr for Label

-- #eval initMultiExec
--   (Theory (Fin 1)
--     -- replica_state (Fin 1) (Fin 1) (Fin 1)
--     )
--   (State (Fin 1)
--     -- replica_state (Fin 1) (Fin 1) (Fin 1)
--     (FieldConcreteType (Fin 1)
--       -- replica_state (Fin 1) (Fin 1) (Fin 1)
--       ))
--   (Fin 1)
--   -- replica_state (Fin 1) (Fin 1) (Fin 1)
--   (FieldConcreteType (Fin 1)
--     -- replica_state (Fin 1) (Fin 1) (Fin 1)
--     )
--   {-- zero := 0,
--     -- one := 0, /- no_op := 0, leader := 0, -/
--     -- member := fun x y=> true
--     : Theory (Fin 1)
--       -- replica_state (Fin 1) (Fin 1) (Fin 1)
--       }
--   default



import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
/-
  This is a simplified version of the NOPaxos protocol, without view
  changes. As such, the leader is modelled as fixed.
-/
veil module NOPaxos

type replica

-- Network
relation m_client_request (v : replica)
relation m_marked_client_request  (dest : replica) (v : replica) (sess_msg_num : replica)
relation m_request_reply (sender : replica) (request : replica) (log_slot_num : replica)
relation m_slot_lookup (dest : replica) (sender : replica) (sess_msg_num : replica)
relation m_gap_commit (dest : replica) (slot_num : replica)
relation m_gap_commit_rep (dest : replica) (sender : replica) (slot_num : replica)

-- Ghost state
relation gh_r_received_sequenced_client_request (r : replica) (s : replica)
relation gh_r_received_drop_notification (r : replica) (s : replica)
relation gh_committed (s : replica) (v : replica)

#gen_state

-- set_option trace.veil.debug true
-- after_init {
--   m_client_request V := false
--   m_marked_client_request D V SMN := false

--   m_client_request V := false
--   m_marked_client_request D V SMN := false
--   m_request_reply S V LSN := false
--   m_slot_lookup D S SMN := false
--   m_gap_commit D SN := false
--   m_gap_commit_rep D S SN := false

--   gh_r_received_sequenced_client_request R S := false
--   gh_r_received_drop_notification R S := false
--   gh_committed S V := false
-- }

def initializer {__veil_mode : Veil.Mode} {ρ σ replica : Type} [replica_dec_eq : DecidableEq replica]
  [replica_inhabited : Inhabited replica] {χ : State.Label → Type}
  [χ_rep :
    (f : State.Label) →
      Veil.FieldRepresentation (State.Label.toDomain replica f) (State.Label.toCodomain replica f) (χ f)]
  [χ_rep_lawful :
    ∀ (f : State.Label),
      Veil.LawfulFieldRepresentation (State.Label.toDomain replica f) (State.Label.toCodomain replica f) (χ f)
        (χ_rep f)]
  [σ_sub : IsSubStateOf (State replica χ) σ] [ρ_sub : IsSubReaderOf (Theory replica) ρ] :
  Veil.VeilExecM __veil_mode ρ σ PUnit.{1} :=
do
        let ⟨⟩ := ()
        let mut __veil_state := (← MonadState.get)
        let mut m_client_request_conc := __veil_state.m_client_request
        let mut m_client_request : replica -> Bool := (χ_rep _).get m_client_request_conc
        let mut m_marked_client_request_conc := __veil_state.m_marked_client_request
        let mut m_marked_client_request : replica -> replica -> replica -> Bool :=
          (χ_rep _).get m_marked_client_request_conc
        let mut m_request_reply_conc := __veil_state.m_request_reply
        let mut m_request_reply : replica -> replica -> replica -> Bool := (χ_rep _).get m_request_reply_conc
        let mut m_slot_lookup_conc := __veil_state.m_slot_lookup
        let mut m_slot_lookup : replica -> replica -> replica -> Bool := (χ_rep _).get m_slot_lookup_conc
        let mut m_gap_commit_conc := __veil_state.m_gap_commit
        let mut m_gap_commit : replica -> replica -> Bool := (χ_rep _).get m_gap_commit_conc
        let mut m_gap_commit_rep_conc := __veil_state.m_gap_commit_rep
        let mut m_gap_commit_rep : replica -> replica -> replica -> Bool := (χ_rep _).get m_gap_commit_rep_conc
        let mut gh_r_received_sequenced_client_request_conc := __veil_state.gh_r_received_sequenced_client_request
        let mut gh_r_received_sequenced_client_request : replica -> replica -> Bool :=
          (χ_rep _).get gh_r_received_sequenced_client_request_conc
        let mut gh_r_received_drop_notification_conc := __veil_state.gh_r_received_drop_notification
        let mut gh_r_received_drop_notification : replica -> replica -> Bool :=
          (χ_rep _).get gh_r_received_drop_notification_conc
        let mut gh_committed_conc := __veil_state.gh_committed
        let mut gh_committed : replica -> replica -> Bool := (χ_rep _).get gh_committed_conc
        let __veil_theory := (← MonadReader.read)
        let __veil_bind_m_client_request0 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.m_client_request) 1 Option.none))
            (fun V => (false)) m_client_request_conc
        m_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_client_request0, { st with m_client_request := __veil_bind_m_client_request0 })))
        m_client_request := @id (replica -> Bool) ((χ_rep _).get m_client_request_conc)
        let __veil_bind_m_marked_client_request0 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.m_marked_client_request) 3 Option.none
                Option.none Option.none))
            (fun D V SMN => (false)) m_marked_client_request_conc
        m_marked_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_marked_client_request0,
                  { st with m_marked_client_request := __veil_bind_m_marked_client_request0 })))
        m_marked_client_request :=
          @id (replica -> replica -> replica -> Bool) ((χ_rep _).get m_marked_client_request_conc)
        let __veil_bind_m_client_request01 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.m_client_request) 1 Option.none))
            (fun V => (false)) m_client_request_conc
        m_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_client_request01, { st with m_client_request := __veil_bind_m_client_request01 })))
        m_client_request := @id (replica -> Bool) ((χ_rep _).get m_client_request_conc)
        let __veil_bind_m_marked_client_request01 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.m_marked_client_request) 3 Option.none
                Option.none Option.none))
            (fun D V SMN => (false)) m_marked_client_request_conc
        m_marked_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_marked_client_request01,
                  { st with m_marked_client_request := __veil_bind_m_marked_client_request01 })))
        m_marked_client_request :=
          @id (replica -> replica -> replica -> Bool) ((χ_rep _).get m_marked_client_request_conc)
        let __veil_bind_m_request_reply0 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.m_request_reply) 3 Option.none
                Option.none Option.none))
            (fun S V LSN => (false)) m_request_reply_conc
        m_request_reply_conc ←
          MonadState.modifyGet
              (fun st => ((__veil_bind_m_request_reply0, { st with m_request_reply := __veil_bind_m_request_reply0 })))
        m_request_reply := @id (replica -> replica -> replica -> Bool) ((χ_rep _).get m_request_reply_conc)
        let __veil_bind_m_slot_lookup0 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.m_slot_lookup) 3 Option.none
                Option.none Option.none))
            (fun D S SMN => (false)) m_slot_lookup_conc
        m_slot_lookup_conc ←
          MonadState.modifyGet
              (fun st => ((__veil_bind_m_slot_lookup0, { st with m_slot_lookup := __veil_bind_m_slot_lookup0 })))
        m_slot_lookup := @id (replica -> replica -> replica -> Bool) ((χ_rep _).get m_slot_lookup_conc)
        let __veil_bind_m_gap_commit0 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.m_gap_commit) 2 Option.none
                Option.none))
            (fun D SN => (false)) m_gap_commit_conc
        m_gap_commit_conc ←
          MonadState.modifyGet
              (fun st => ((__veil_bind_m_gap_commit0, { st with m_gap_commit := __veil_bind_m_gap_commit0 })))
        m_gap_commit := @id (replica -> replica -> Bool) ((χ_rep _).get m_gap_commit_conc)
        let __veil_bind_m_gap_commit_rep0 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.m_gap_commit_rep) 3 Option.none
                Option.none Option.none))
            (fun D S SN => (false)) m_gap_commit_rep_conc
        m_gap_commit_rep_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_m_gap_commit_rep0, { st with m_gap_commit_rep := __veil_bind_m_gap_commit_rep0 })))
        m_gap_commit_rep := @id (replica -> replica -> replica -> Bool) ((χ_rep _).get m_gap_commit_rep_conc)
        let __veil_bind_gh_r_received_sequenced_client_request0 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.gh_r_received_sequenced_client_request)
                2 Option.none Option.none))
            (fun R S => (false)) gh_r_received_sequenced_client_request_conc
        gh_r_received_sequenced_client_request_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_gh_r_received_sequenced_client_request0,
                  { st with
                    gh_r_received_sequenced_client_request := __veil_bind_gh_r_received_sequenced_client_request0 })))
        gh_r_received_sequenced_client_request :=
          @id (replica -> replica -> Bool) ((χ_rep _).get gh_r_received_sequenced_client_request_conc)
        let __veil_bind_gh_r_received_drop_notification0 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.gh_r_received_drop_notification) 2
                Option.none Option.none))
            (fun R S => (false)) gh_r_received_drop_notification_conc
        gh_r_received_drop_notification_conc ←
          MonadState.modifyGet
              (fun st =>
                ((__veil_bind_gh_r_received_drop_notification0,
                  { st with gh_r_received_drop_notification := __veil_bind_gh_r_received_drop_notification0 })))
        gh_r_received_drop_notification :=
          @id (replica -> replica -> Bool) ((χ_rep _).get gh_r_received_drop_notification_conc)
        let __veil_bind_gh_committed0 :=
          (χ_rep _).setSingle
            (veil_dsimp% [fieldRepresentationPatSimp]
              (Veil.FieldUpdatePat.pad (State.Label.toDomain replica State.Label.gh_committed) 2 Option.none
                Option.none))
            (fun S V => (false)) gh_committed_conc
        gh_committed_conc ←
          MonadState.modifyGet
              (fun st => ((__veil_bind_gh_committed0, { st with gh_committed := __veil_bind_gh_committed0 })))
        gh_committed := @id (replica -> replica -> Bool) ((χ_rep _).get gh_committed_conc)

-- set_option maxHeartbeats 10000000
-- #time #gen_spec

-- #time #check_invariants

open Lean Meta Elab Command Veil in
scoped elab "⌞? " t:term " ⌟" : term => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  Term.elabTerm (← `(term| $t $(← mod.sortIdents)*)) none

-- #time #check_invariants
section

veil_variables

omit χ χ_rep χ_rep_lawful

open Veil Extract

variable [FinEnum replica] [Hashable replica]

def instFinEnumForComponents (f : State.Label)
  : (IteratedProd <| List.map FinEnum <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    infer_instance_for_iterated_prod

instance instDecidableEqForComponents'' (f : State.Label)
  : DecidableEq (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

instance instHashableForComponents' (f : State.Label)
  : Hashable (IteratedProd' <| (⌞? State.Label.toDomain ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd', State.Label.toDomain] <;>
    infer_instance

abbrev FieldConcreteType (f : State.Label) : Type :=
  match f with
  | State.Label.m_client_request => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_client_request)
  | State.Label.m_marked_client_request => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_marked_client_request)
  | State.Label.m_request_reply => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_request_reply)
  | State.Label.m_slot_lookup => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_slot_lookup)
  | State.Label.m_gap_commit  => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_gap_commit)
  | State.Label.m_gap_commit_rep => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.m_gap_commit_rep)
  | State.Label.gh_r_received_sequenced_client_request => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.gh_r_received_sequenced_client_request)
  | State.Label.gh_r_received_drop_notification => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.gh_r_received_drop_notification)
  | State.Label.gh_committed => Std.HashSet (IteratedProd' <| (⌞? State.Label.toDomain ⌟) State.Label.gh_committed)

instance instReprForComponents  [Repr replica]
  -- [Repr replica_state] [Repr value] [Repr quorum] [Repr seq_t]
  (f : State.Label)
  : Repr ((⌞? FieldConcreteType ⌟) f) := by
  cases f <;>
    dsimp only [IteratedProd, IteratedProd', List.foldr, FieldConcreteType, State.Label.toDomain, State.Label.toCodomain] <;>
    infer_instance

instance : Inhabited ((⌞? State ⌟) (⌞? FieldConcreteType ⌟)) := by
  constructor ; constructor <;>
  dsimp only [FieldConcreteType, State.Label.toCodomain] <;>
  exact default

instance rep (f : State.Label) : FieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f) := -- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
    | State.Label.m_client_request =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_client_request)
    | State.Label.m_marked_client_request =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_marked_client_request)
    | State.Label.m_request_reply =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_request_reply)
    | State.Label.m_slot_lookup =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_slot_lookup)
    | State.Label.m_gap_commit =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit)
    | State.Label.m_gap_commit_rep =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit_rep)
    | State.Label.gh_r_received_sequenced_client_request =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_sequenced_client_request)
    | State.Label.gh_r_received_drop_notification =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_drop_notification)
    | State.Label.gh_committed =>
      instFinsetLikeAsFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_committed)

#check  FinsetLike

instance lawful (f : State.Label) : LawfulFieldRepresentation
  ((⌞? State.Label.toDomain ⌟) f)
  ((⌞? State.Label.toCodomain ⌟) f)
  ((⌞? FieldConcreteType ⌟) f)
  ((⌞? rep ⌟) f) :=-- by cases f <;> apply instFinsetLikeAsFieldRep <;> apply instFinEnumForComponents
  match f with
    | State.Label.m_client_request =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_client_request)
    | State.Label.m_marked_client_request =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_marked_client_request)
    | State.Label.m_request_reply =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_request_reply)
    | State.Label.m_slot_lookup =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_slot_lookup)
    | State.Label.m_gap_commit =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit)
    | State.Label.m_gap_commit_rep =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.m_gap_commit_rep)
    | State.Label.gh_r_received_sequenced_client_request =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_sequenced_client_request)
    | State.Label.gh_r_received_drop_notification =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_r_received_drop_notification)
    | State.Label.gh_committed =>
      instFinsetLikeLawfulFieldRep (IteratedProd'.equiv) ((⌞? instFinEnumForComponents ⌟) State.Label.gh_committed)
end

/-
attribute [local dsimpFieldRepresentationGet, local dsimpFieldRepresentationSet]
  instFinEnumForComponents in
-- attribute [local dsimpFieldRepresentationGet] FourNodes.equiv_IteratedProd in
#specialize_nextact with FieldConcreteType
  injection_begin
    [FinEnum replica] [Hashable replica]
  injection_end => NextAct'

#gen_executable_list! log_entry_being Std.Format
  targeting NextAct'
  injection_begin
    [FinEnum replica] [Hashable replica]
  injection_end

#check initMultiExec
#check nextActMultiExec
-/
simple_deriving_repr_for' State
-- deriving instance Repr for Label

#eval initializer (__veil_mode := Veil.Mode.external)
  (ρ := Theory (Fin 1)
    -- replica_state (Fin 1) (Fin 1) (Fin 1)
    )
  (σ := State (Fin 1)
    -- replica_state (Fin 1) (Fin 1) (Fin 1)
    (FieldConcreteType (Fin 1)
      -- replica_state (Fin 1) (Fin 1) (Fin 1)
      ))
  (replica := Fin 1)
  -- replica_state (Fin 1) (Fin 1) (Fin 1)
  (χ := FieldConcreteType (Fin 1)
    -- replica_state (Fin 1) (Fin 1) (Fin 1)
    )
  {-- zero := 0,
    -- one := 0, /- no_op := 0, leader := 0, -/
    -- member := fun x y=> true
    : Theory (Fin 1)
      -- replica_state (Fin 1) (Fin 1) (Fin 1)
      }
  default
