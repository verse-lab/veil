import Veil.DSL

-- https://github.com/aman-goel/ivybench/blob/d2c9298fdd099001c71a34bc2e118db6f07d8404/multisig/ivy/multisig-all.ivy


section MultiSigAll
open Classical

type validator
type destination
type value
type deadline
type signature

relation holding : validator → Prop
relation collect : validator → destination → value → deadline → Prop

relation sig : validator → destination → value → deadline → signature → Prop
relation sig_auth : signature → Prop

relation proposed : validator → destination → value → deadline → Prop
relation paid : validator → destination → value → deadline → Prop
relation cancelled : validator → destination → value → deadline → Prop

relation expired : deadline → Prop

#gen_state MultiSigAll

after_init {
  holding N := True;
  collect N K V D := False;

  proposed N K V D := False;
  paid N K V D := False;
  cancelled N K V D := False;

  sig N K V D S := False
}

action propose (n: validator) (k: destination) (v: value) (d: deadline) = {
  require holding n;
  require ¬ collect n k v d;
  require ¬ paid n k v d;
  holding n := False;
  collect n k v d := True;
  sig n k v d S := False;
  proposed n k v d := True
}

action add_sig (n: validator) (k: destination) (v: value) (d: deadline) (s: signature) = {
  require ¬ expired d;
  require sig_auth s;
  sig n k v d s := True
}

action pay (n: validator) (k: destination) (v: value) (d: deadline) = {
  require collect n k v d;
  require ¬ expired d;
  require sig n k v d S;
  paid n k v d := True;
  holding n := True;
  collect n k v d := False
}

action cancel (n: validator) (k: destination) (v: value) (d: deadline) = {
  require collect n k v d;
  require expired d;
  cancelled n k v d := True;
  holding n := True;
  collect n k v d := False
}

action expire (d: deadline) = {
  expired d := True
}

safety [cancelled_after_deadline] cancelled N K V D → expired D
safety [paid_if_enough_sigs] paid N K V D → (∀ s, sig N K V D s ∧ sig_auth s)
safety [paid] paid N K V D → proposed N K V D

invariant [ic3po_global2] collect V1 D1 V2 D2 → proposed V1 D1 V2 D2
invariant [ic3po_global3] sig V1 D1 V2 D2 S1 → sig_auth S1
#gen_spec MultiSigAll

#check_invariants
