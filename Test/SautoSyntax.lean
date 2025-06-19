import Veil

#guard_msgs(drop warning) in
theorem foo : ∀ (p q : Prop), p → (p → q) → q := by intro p q hp hpq; sauto [hp, hpq]

set_option veil.smt.reconstructProofs true
#guard_msgs in
theorem foo_recon : ∀ (p q : Prop), p → (p → q) → q := by intro p q hp hpq; sauto [hp, hpq]
