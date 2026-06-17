import Veil

/-
Original source/reference:
- Local modeling analogues:
  - Examples/Ivy/DecentralizedLock.lean (epoched authority transfer)
  - Examples/TLA/Raft.lean (leader failover)
- Production inspiration: etcd lease checkpoint persistence across leader
  failover (etcd-io/etcd#13508)

Bug/race shape:
A leader checkpoints a lease's reduced remaining TTL. After failover, the new
leader forgets that checkpointed TTL and reconstructs the lease from the older
grant state, reviving a lease that should already be considered expired.

Why #simulate here:
The violating trace is short, but exhaustive search must branch over leaders,
leases, epochs, and recovery schedules.
-/

veil module CheckpointLeaseFailover

type node
type epoch
type lease

instantiate epochOrd : TotalOrder epoch

individual leader : node
immutable individual initial_leader : node
immutable individual initial_epoch : epoch
relation current_epoch (e : epoch)
relation granted_until (l : lease) (e : epoch)
relation checkpointed_until (l : lease) (e : epoch)
relation active_on_leader (l : lease)

#gen_state

after_init {
  leader := initial_leader
  current_epoch E := E == initial_epoch
  granted_until L E := false
  checkpointed_until L E := false
  active_on_leader L := false
}

action grantLease (l : lease) (expiry : epoch) {
  require ∀ now, current_epoch now -> ¬ epochOrd.le expiry now
  granted_until l E := E == expiry
  active_on_leader l := true
}

action checkpointRemainingTTL (l : lease) (expiry : epoch) {
  require active_on_leader l
  require ∀ now, current_epoch now -> ¬ epochOrd.le expiry now
  checkpointed_until l E := E == expiry
}

action failover (newLeader : node) (newEpoch : epoch) {
  require newLeader != leader
  require ∀ oldEpoch, current_epoch oldEpoch -> ¬ epochOrd.le newEpoch oldEpoch
  leader := newLeader
  current_epoch E := E == newEpoch
  active_on_leader L := false
}

action recoverLeaseFromGrant (l : lease) (expiry : epoch) {
  require granted_until l expiry
  active_on_leader l := true
}

invariant [one_current_epoch]
  ∀ (e1 e2 : epoch), current_epoch e1 ∧ current_epoch e2 -> e1 = e2

safety [checkpointed_expiry_respected]
  ∀ (l : lease) (expiry now : epoch),
    checkpointed_until l expiry ∧ current_epoch now ∧ epochOrd.le expiry now ->
      ¬ active_on_leader l

#gen_spec

-- model_check must branch over failovers, recovery choices, and many lease/epoch combinations.
-- set_option veil.violationIsError false in
-- #model_check { node := Fin 12, epoch := Fin 8, lease := Fin 8 }
--   { initial_leader := (0 : Fin 12), initial_epoch := (0 : Fin 8) }

-- simulate quickly finds the stale-recovery bug after failover.
set_option veil.violationIsError false in
#simulate { node := Fin 12, epoch := Fin 8, lease := Fin 8 }
  { initial_leader := (0 : Fin 12), initial_epoch := (0 : Fin 8) }
  (seed := 23) (maxTraces := 2000) (maxSteps := 10)

end CheckpointLeaseFailover
