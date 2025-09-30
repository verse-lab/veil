import Veil

-- https://github.com/aman-goel/ivybench/blob/d2c9298fdd099001c71a34bc2e118db6f07d8404/multisig/ivy/multisig-all.ivy


veil module MultiSigAll

type validator
type destination
type value
type deadline
type signature

relation holding : validator → Bool
relation collect : validator → destination → value → deadline → Bool

relation sig : validator → destination → value → deadline → signature → Bool
relation sig_auth : signature → Bool

relation proposed : validator → destination → value → deadline → Bool
relation paid : validator → destination → value → deadline → Bool
relation cancelled : validator → destination → value → deadline → Bool

relation expired : deadline → Bool

#gen_state

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
  require ¬ expired d;
  require sig_auth s;
  sig n k v d s := true
}

action pay (n: validator) (k: destination) (v: value) (d: deadline) {
  require collect n k v d;
  require ¬ expired d;
  require ∀ S, sig n k v d S;
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
safety [paid_if_enough_sigs] paid N K V D → (∀ s, sig N K V D s ∧ sig_auth s)
safety [paid_imp_proposed] paid N K V D → proposed N K V D

invariant [ic3po_global2] collect V1 D1 V2 D2 → proposed V1 D1 V2 D2
invariant [ic3po_global3] sig V1 D1 V2 D2 S1 → sig_auth S1

#time #gen_spec

end MultiSigAll
