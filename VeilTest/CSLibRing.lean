module

public import Examples.Ring.RingRef

public section

namespace CSLibRingTest

open Veil.RelationalTransitionSystem RingRef

-- Importing the example exposes a CSLib simulation and the concrete safety theorem.
example (th : RingConc.Theory) (hnodup : th.allNodes.Nodup)
    (hlen : 1 < th.allNodes.length) [NeZero th.allNodes.length] :
    Cslib.LTS.IsSimulation (concreteLTS th) (abstractLTS th).saturate (rel th) :=
  sim th hnodup hlen

example (th : RingConc.Theory) (hnodup : th.allNodes.Nodup)
    (hlen : 1 < th.allNodes.length) [NeZero th.allNodes.length] :
    Cslib.LTS.IsSimulation (concreteLTS th).saturate (abstractLTS th).saturate (rel th) :=
  (sim th hnodup hlen).isSimulation_saturate_left

example (th : RingConc.Theory) (st : RingConc.State RingConc.FieldAbstractType)
    (hr : RingConc.relationalTransitionSystem.reachable th st) :
    st.leader.length ≤ 1 := single_leader_holds th st hr

-- The ring order differs from the identifier order, as allowed by the proof.
private def theory : RingConc.Theory := ⟨[7, 2, 9]⟩
private instance : NeZero theory.allNodes.length := ⟨by decide⟩
private abbrev State := RingConc.State RingConc.FieldAbstractType
private def queued (leaders : List Nat) (src dst : Nat) : State :=
  ⟨leaders, [⟨9, src, dst⟩]⟩

private theorem send_empty (leaders : List Nat) :
    CC.tr theory ⟨leaders, []⟩ .send (queued leaders 9 7) := by
  rw [cc_send]
  refine ⟨9, by decide, ?_⟩
  rfl

private theorem forward_first (leaders : List Nat) :
    CC.tr theory (queued leaders 9 7) .recv (queued leaders 7 2) := by
  rw [cc_recv]
  refine ⟨⟨9, 9, 7⟩, by simp [queued], ?_⟩
  simp [queued, RingConc.nextNode, theory]
  rfl

private theorem forward_second (leaders : List Nat) :
    CC.tr theory (queued leaders 7 2) .recv (queued leaders 2 9) := by
  rw [cc_recv]
  refine ⟨⟨9, 7, 2⟩, by simp [queued], ?_⟩
  simp [queued, RingConc.nextNode, theory]
  rfl

/-- A concrete trace that elects 9, then sends its token around the ring again.
It exercises both a duplicate-send stutter and the receive case that the
simulation matches with abstract `recv; send`. -/
private theorem execution :
    (CC.toLTS theory).MTr (⟨[], []⟩ : State)
      [.send, .send, .recv, .recv, .recv, .send, .recv, .recv, .recv]
      (queued [9] 9 7) := by
  have duplicate : CC.tr theory (queued [] 9 7) .send (queued [] 9 7) := by
    rw [cc_send]
    refine ⟨9, by decide, ?_⟩
    simp [queued, show RingConc.nextNode 9 theory = 7 from rfl]
  have elect : CC.tr theory (queued [] 2 9) .recv ⟨[9], []⟩ := by
    rw [cc_recv]
    refine ⟨⟨9, 2, 9⟩, by simp [queued], ?_⟩
    simp [queued]
  have reemit : CC.tr theory (queued [9] 2 9) .recv (queued [9] 9 7) := by
    rw [cc_recv]
    refine ⟨⟨9, 2, 9⟩, by simp [queued], ?_⟩
    simp [queued, show RingConc.nextNode 9 theory = 7 from rfl, List.insertOrdered]
  exact .stepL (send_empty []) (.stepL duplicate
    (.stepL (forward_first []) (.stepL (forward_second []) (.stepL elect
      (.stepL (send_empty [9]) (.stepL (forward_first [9])
        (.stepL (forward_second [9]) (.single _ reemit))))))))

/-- The same nine-step trace is matched with the same observations. Each
saturated receive contains exactly one actual abstract receive, while τ edges
can expand to any finite sequence of sends, including none. -/
private theorem matching_execution :
    ∃ sa₀ sa, (CA (node := RNode theory.allNodes)).init ⟨⟩ sa₀ ∧
      (abstractLTS theory).saturate.MTr sa₀
        [.τ, .τ, .receive, .receive, .receive, .τ, .receive, .receive, .receive] sa ∧
      rel theory (queued [9] 9 7) sa := by
  obtain ⟨sa₀, hi, hr⟩ := initially_related theory (⟨[], []⟩ : State)
    ((cc_init _ _).mpr rfl)
  obtain ⟨sa, hs, hr'⟩ := (sim theory (by decide) (by decide)).sim_trace hr _ _
    (observed_mTr_of_mTr observeConcrete execution)
  exact ⟨sa₀, sa, hi, hs, hr'⟩

private theorem final_reachable : CC.reachable theory (queued [9] 9 7) := by
  apply reachable_of_mTr (s := (⟨[], []⟩ : State)) ?_ execution
  exact .init _ ((cc_assumptions _).mpr (by decide)) ((cc_init _ _).mpr rfl)

example : (queued [9] 9 7).leader.length ≤ 1 :=
  single_leader_holds theory _ final_reachable

-- Check the entire imported proof chain, including reconstructed SMT proofs.
-- No admitted proof, trusted SMT axiom, or extra protocol axiom is permitted.
open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``RingAbs.single_leader.is_inv, ``RingRef.sim,
      ``RingRef.single_leader_safety, ``execution, ``matching_execution, ``final_reachable] do
    for ax in ← collectAxioms name do
      unless allowed.contains ax do
        throwError "unexpected axiom {ax} in {name}"

end CSLibRingTest
