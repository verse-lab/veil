module

public import Veil
public meta import Lean.Util.CollectAxioms

set_option veil.smt.trust false

/-! Four concrete instances, three sorts, two ordinary parameters and nine
invariant clauses. Reachable-invariant export must keep the checked WP
certificates folded rather than expanding the whole composed initializer. -/

veil module ExportScaleVenue

type seat
relation opened : seat → Bool
relation blocked : seat → Bool

after_init {
  opened S := false
  blocked S := false
}

action open_seat (s : seat) {
  require blocked s = false
  opened s := true
  ensure ∀ t : seat, old(opened t) → opened t
}

action block_seat (s : seat) {
  require ¬ opened s
  blocked s := true
  ensure ∀ t : seat, opened t ↔ old(opened t)
}

invariant [open_unblocked] ∀ s : seat, opened s → ¬ blocked s

#gen_spec
end ExportScaleVenue


veil module ExportScaleAllocator

type seat
type agent
param venue : ExportScaleVenue seat

relation assigned : seat → agent → Bool

after_init { assigned S A := false }

procedure grant (s : seat) (a : agent) {
  require venue.opened s
  require ∀ b : agent, ¬ assigned s b
  assigned s a := true
  ensure ∀ (t : seat) (b : agent), assigned t b ↔ old(assigned t b) ∨ (t = s ∧ b = a)
}

action assign (s : seat) (a : agent) {
  require venue.opened s
  require ∀ b : agent, ¬ assigned s b
  grant s a
  ensure ∀ (t : seat) (b : agent), old(assigned t b) → assigned t b
}

invariant [assigned_open] ∀ (s : seat) (a : agent), assigned s a → venue.opened s
invariant [single_desk] ∀ (s : seat) (a b : agent), assigned s a ∧ assigned s b → a = b

#gen_spec
end ExportScaleAllocator


veil module ExportScaleOffice

type seat
type agent
type customer
param desk : agent
param alloc : ExportScaleAllocator seat agent

relation sold : seat → customer → Bool

after_init { sold S C := false }

procedure record_sale (s : seat) (c : customer) {
  require ∀ d : customer, ¬ sold s d
  sold s c := true
  ensure ∀ (t : seat) (d : customer), sold t d ↔ old(sold t d) ∨ (t = s ∧ d = c)
}

action sell (s : seat) (c : customer) {
  require alloc.assigned s desk
  require ∀ d : customer, ¬ sold s d
  record_sale s c
  ensure sold s c
}

action refund (s : seat) (c : customer) {
  require sold s c
  sold s c := false
  ensure ∀ (t : seat) (d : customer), sold t d → old(sold t d)
}

invariant [sold_assigned] ∀ (s : seat) (c : customer), sold s c → alloc.assigned s desk
invariant [one_customer] ∀ (s : seat) (c d : customer), sold s c ∧ sold s d → c = d

#gen_spec
end ExportScaleOffice


veil module ExportScaleSystem

type seat
type agent
type customer
param eastDesk : agent
param westDesk : agent

isolate venue : ExportScaleVenue (seat := seat)
isolate alloc : ExportScaleAllocator (seat := seat) (agent := agent) (venue := venue) with venue
isolate east : ExportScaleOffice (seat := seat) (agent := agent) (customer := customer)
  (desk := eastDesk) (alloc := alloc) with alloc
isolate west : ExportScaleOffice (seat := seat) (agent := agent) (customer := customer)
  (desk := westDesk) (alloc := alloc) with alloc

-- Assumptions follow the isolates, once the composite's state is complete.
assumption [distinct_desks] eastDesk ≠ westDesk

safety [sold_seats_open]
  ∀ (s : seat) (c : customer), (east.sold s c ∨ west.sold s c) → venue.opened s ∧ ¬ venue.blocked s

safety [no_double_booking]
  ∀ (s : seat) (c d : customer),
    (east.sold s c ∨ west.sold s c) ∧ (east.sold s d ∨ west.sold s d) → c = d

#gen_spec
#check_invariants
#gen_theorems

#check sold_seats_open.is_inv
#check no_double_booking.is_inv

run_cmd do
  for name in [`ExportScaleSystem.Invariants.is_inv,
      `ExportScaleSystem.no_double_booking.is_inv,
      `ExportScaleSystem.sold_seats_open.is_inv] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected proof dependency for {name}: {axioms}"
end ExportScaleSystem
