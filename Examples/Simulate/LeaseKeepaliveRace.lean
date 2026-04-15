import Veil

/-
Original source/reference:
- Closest local modeling analogue: Examples/Ivy/DecentralizedLock.lean
- Production reference: etcd KeepAlive vs lease-expiry revocation race
  (etcd-io/etcd#21389, issue #14758)

Bug/race shape:
A client still has keys attached to a lease when revocation starts. A late
keepalive succeeds after revocation has already removed the keys, so the client
appears renewed even though its data is gone.

Why #simulate here:
The bad trace is only a handful of steps, but exhaustive search must branch over
clients, keys, revoke timing, and keepalive interleavings.
-/

veil module LeaseKeepaliveRace

type client
type key

relation lease_alive (c : client)
relation revoke_started (c : client)
relation keepalive_succeeded (c : client)
relation key_attached (c : client) (k : key)
relation key_present (k : key)

#gen_state

after_init {
  lease_alive C := false
  revoke_started C := false
  keepalive_succeeded C := false
  key_attached C K := false
  key_present K := false
}

action grantLease (c : client) {
  require !(lease_alive c)
  lease_alive c := true
  revoke_started c := false
  keepalive_succeeded c := false
}

action attachKey (c : client) (k : key) {
  require lease_alive c
  key_attached c k := true
  key_present k := true
}

action startRevoke (c : client) {
  require lease_alive c
  revoke_started c := true
  lease_alive c := false
}

action deleteKey (c : client) (k : key) {
  require revoke_started c
  require key_attached c k
  key_present k := false
}

action keepAlive (c : client) {
  require revoke_started c
  keepalive_succeeded c := true
  lease_alive c := true
}

safety [renewal_keeps_keys_live]
  ∀ (c : client) (k : key), keepalive_succeeded c ∧ key_attached c k -> key_present k

#gen_spec

-- model_check must branch over clients, keys, revoke order, and late keepalives.
-- set_option veil.violationIsError false in
-- #model_check { client := Fin 8, key := Fin 8 } {}

-- simulate usually hits the keepalive-after-revoke race in a short trace.
set_option veil.violationIsError false in
#simulate { client := Fin 8, key := Fin 8 } {}
  (seed := 11) (maxTraces := 300) (maxSteps := 12)

end LeaseKeepaliveRace
