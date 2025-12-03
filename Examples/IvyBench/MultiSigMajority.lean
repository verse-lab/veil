import Veil
import Veil.Core.Tools.Checker.Concrete.Main
-- https://github.com/aman-goel/ivybench/blob/d2c9298fdd099001c71a34bc2e118db6f07d8404/multisig/ivy/multisig-majority.ivy


veil module MultiSigMaj

type validator
type destination
type value
type deadline
type signature
type quorum

relation holding : validator → Bool
relation collect : validator → destination → value → deadline → Bool

relation sig : validator → destination → value → deadline → signature → Bool
relation sig_auth : signature → Bool

relation proposed : validator → destination → value → deadline → Bool
relation paid : validator → destination → value → deadline → Bool
relation cancelled : validator → destination → value → deadline → Bool

relation expired : deadline → Bool

immutable relation member : signature → quorum → Bool

#gen_state
ghost relation chosenAt (Q:quorum) (N:validator) (K:destination) (V:value) (D:deadline) := ∀ S, member S Q -> sig N K V D S
ghost relation chosen (N:validator) (K:destination) (V:value) (D:deadline) := ∃ q, chosenAt q N K V D

assumption ∀ (q1 q2 : quorum), ∃ (s : signature), member s q1 ∧ member s q2

after_init {
  holding N := true;
  collect N K V D := false;

  proposed N K V D := false;
  paid N K V D := false;
  cancelled N K V D := false;

  sig N K V D S := false
}

action propose (n: validator) (k: destination) (v: value) (d: deadline) {
  require holding n;
  require ¬ collect n k v d;
  require ¬ paid n k v d;
  holding n := false;
  collect n k v d := true;
  sig n k v d S := false;
  proposed n k v d := true
}

action add_sig (n: validator) (k: destination) (v: value) (d: deadline) (s: signature) {
  require collect n k v d;
  require ¬ expired d;
  require sig_auth s;
  sig n k v d s := true
}

action pay (n: validator) (k: destination) (v: value) (d: deadline) {
  require collect n k v d;
  require ¬ expired d;
  require chosen n k v d;

  paid n k v d := true;
  holding n := true;
  collect n k v d := false
}

action cancel (n: validator) (k: destination) (v: value) (d: deadline) {
  require collect n k v d;
  require expired d;

  cancelled n k v d := true;
  holding n := true;
  collect n k v d := false
}

action expire (d: deadline) {
  expired d := true
}

safety [cancelled_after_deadline] cancelled N K V D → expired D
safety [paid_if_enough_sigs] paid N K V D → (∃ q, ∀ s, (member s q) → (sig N K V D s ∧ sig_auth s))
safety [paid_imp_proposed] paid N K V D → proposed N K V D

invariant [ic3po_global2] collect V1 D1 V2 D2 → proposed V1 D1 V2 D2
invariant [ic3po_global3] sig V1 D1 V2 D2 S1 → sig_auth S1
termination true = true
#time #gen_spec

#gen_exec
#finitize_types (Fin 2), (Fin 1), (Fin 1), (Fin 1), (Fin 1), (Fin 1)

#set_theory { member := fun s q => true }

#run_checker ic3po_global2
#eval modelCheckerResult.seen.size

end MultiSigMaj
