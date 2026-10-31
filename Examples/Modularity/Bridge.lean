module

public import Veil

set_option veil.smt.trust false

veil module Source

type tx
relation finalized : tx → Bool
after_init { finalized T := false }

action finalize (t : tx) {
  finalized t := true
  ensure ∀ u : tx, old(finalized u) → finalized u
}

#gen_spec
end Source


veil module Adapter

type tx
param source : Source tx

relation relayed : tx → Bool
after_init { relayed T := false }

procedure record (t : tx) {
  require source.finalized t
  relayed t := true
  ensure ∀ u : tx, relayed u ↔ old(relayed u) ∨ u = t
}

action relay (t : tx) {
  require source.finalized t
  record t
  ensure ∀ u : tx, old(relayed u) → relayed u
}

invariant [relay_backed]
  ∀ t : tx, relayed t → source.finalized t

#gen_spec
end Adapter


veil module Destination

type tx
param adapter : Adapter tx

relation minted : tx → Bool
after_init { minted T := false }

action mint (t : tx) {
  require adapter.relayed t ∧ ¬ minted t
  minted t := true
}

invariant [mint_backed]
  ∀ t : tx, minted t → adapter.relayed t

#gen_spec
end Destination


veil module Bridge

type tx

isolate source : Source (tx := tx)
isolate adapter : Adapter (tx := tx) (source := source) with source
isolate destination : Destination (tx := tx) (adapter := adapter) with source, adapter

safety [backed]
  ∀ t : tx, destination.minted t → source.finalized t

#gen_spec
#check_invariants
#gen_theorems
#check backed.is_inv

end Bridge
