module

public import Veil

set_option veil.smt.trust false
set_option veil.printCounterexamples false

veil module RevocableProvider

type transaction
relation finalized : transaction → Bool

after_init { finalized T := false }
action finalize (t : transaction) { finalized t := true }
action revoke (t : transaction) { finalized t := false }

#gen_spec
end RevocableProvider

veil module RevocationConsumer

type transaction
param source : RevocableProvider transaction
relation accepted : transaction → Bool

after_init { accepted T := false }
action accept (t : transaction) {
  require source.finalized t
  accepted t := true
}
invariant [accepted_finalized] ∀ t : transaction, accepted t → source.finalized t

#gen_spec
end RevocationConsumer

veil module RejectedRevocationComposition

type transaction

isolate source : RevocableProvider (transaction := transaction)
isolate consumer : RevocationConsumer (transaction := transaction) (source := source) with source

safety [backed] ∀ t : transaction, consumer.accepted t → source.finalized t

#gen_spec

-- A failed proof is expected here. Inspect the actual foreign-step result
-- below, rather than matching generated internal names in formatted output.
#guard_msgs(drop info, drop warning) in
set_option veil.violationIsError false in
#check_invariants

run_cmd do
  let results ← Veil.Verifier.waitEnabledSync
  let mod ← Veil.getCurrentModule
  let nameFor (name : Lean.Name) :=
    (mod.instanceNames.find? (·.1 == name)).map (·.2)
  let some revoke := nameFor `source.revoke
    | throwError "missing concrete revoke action"
  let some property := nameFor `consumer.accepted_finalized
    | throwError "missing consumer backing invariant"
  unless results.vcs.any (fun vc =>
      match vc.metadata with
      | .induction metadata => metadata.action == revoke && metadata.property == property &&
          vc.status == some .disproven
      | .trace _ => false) do
    throwError "the destructive provider step was not rejected by the consumer's stability check"

#guard_msgs(drop info, drop warning) in
#gen_theorems

run_cmd do
  if (← Lean.getEnv).contains `RejectedRevocationComposition.backed.is_inv then
    throwError "an unconditional safety theorem was exported despite the failed foreign-step obligation"

end RejectedRevocationComposition
