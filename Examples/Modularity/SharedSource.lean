module

public import Examples.Modularity.Bridge

set_option veil.smt.trust false

/-! Both adapters observe the same evolving source. Neither dependency
binding allocates another source or another copy of its finalization history. -/
veil module SharedSource

type tx

isolate source : Source (tx := tx)
isolate first : Adapter (tx := tx) (source := source) with source
isolate second : Adapter (tx := tx) (source := source) with source

safety [both_backed]
  ∀ t : tx, (first.relayed t ∨ second.relayed t) → source.finalized t

#gen_spec
#check_invariants
#gen_theorems

#check both_backed.is_inv

end SharedSource
