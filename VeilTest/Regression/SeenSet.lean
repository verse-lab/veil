module

public import Veil

/-!
`#model_check (seenSet := S)` picks the map type of the shards of the parallel search's seen set
(default `TreeMapShard`). Each state below is reachable along several paths, so the seen set has to
recognize it again; the search must explore the same states whichever map it uses, with either
fingerprint type and in compiled mode.
-/

veil module SeenSet

individual a : Bool
individual b : Bool
individual c : Bool
individual d : Bool

#gen_state

after_init {
  a := false
  b := false
  c := false
  d := false
}

action set_a { a := true }
action set_b { b := true }
action set_c { c := true }
action set_d { d := true }

invariant [consistent] a ∨ ¬ a

#gen_spec

-- The default, `TreeMapShard`.
/-- info: ✅ No violation (explored 16 states) -/
#guard_msgs in
#model_check interpreted {} {}

/-- info: ✅ No violation (explored 16 states) -/
#guard_msgs in
#model_check interpreted {} {} (seenSet := HAMTMapShard)

/-- info: ✅ No violation (explored 16 states) -/
#guard_msgs in
#model_check interpreted {} {} (fingerprintType := UInt64) (seenSet := HAMTMapShard)

/-- info: ✅ No violation (explored 16 states) -/
#guard_msgs in
#model_check compiled {} {} (seenSet := HAMTMapShard)

end SeenSet
