import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

-- Signatures in the symbolic (Dolev-Yao) model

class PKScheme {PubK PrivK Val Sig : Type}
  (sign : Val → PrivK → Sig)
  (verify : Val → Sig → PubK → Bool)
  (keyMap : PubK → PrivK) :=

  /-- Only correctly generated signatures verify. -/
  verifyIffSign : ∀ (v : Val) (pk : PubK) (s : Sig),
    s = sign v (keyMap pk) ↔ verify v s pk

theorem PK_signVerify [pks : @PKScheme PubK PrivK Val Sig sign verify keyMap] :
  ∀ (v : Val) (pk : PubK), verify v (sign v (keyMap pk)) pk = true := by
    intro v pk
    have ⟨H, _⟩ := pks.verifyIffSign v pk (sign v (keyMap pk))
    apply H ; rfl

class ThresholdScheme {PubK PrivK Val LightSig CombinedSig : Type}
  (N : ℕ)
  (thres : ℕ)
  (lightSign : Val → PrivK → LightSig)
  (lightVerify : Val → LightSig → PubK → Bool)
  (keyMap : PubK → PrivK)
  (combine : List LightSig → CombinedSig)
  (verify : Val → CombinedSig → Bool) :=

  /-- Only correctly generated light signatures verify. -/
  lightVerifyIffSign : ∀ (v : Val) (pk : PubK) (s : LightSig),
    s = lightSign v (keyMap pk) ↔ lightVerify v s pk

  /-- Combined signatures verify iff they are the combination of
    a sufficient number of valid light signatures.-/
  verifyIffSign : ∀ (v : Val) (cs : CombinedSig),
    (∃ pks : List PubK,
      List.Nodup pks ∧ pks.length = thres ∧
      pks.length = N - thres ∧
      cs = combine (List.map (λ pk => lightSign v (keyMap pk)) pks)) ↔
    verify v cs

theorem Threshold_signVerify [ths : @ThresholdScheme PubK PrivK Val LightSig CombinedSig
   N thres lightSign lightVerify keyMap combine verify] :
  ∀ (v : Val) (pk : PubK), lightVerify v (lightSign v (keyMap pk)) pk := by
    intro v pk
    have ⟨H, _⟩ := ths.lightVerifyIffSign v pk (lightSign v (keyMap pk))
    apply H ; rfl


-- Is this needed?

-- /-- Public-private keypair -/
-- class KeyPair {PubK PrivK : Type} [DecidableEq PubK] :=
--   pub : PubK
--   priv : PrivK

-- /-- Type `A` can be converted into `t`, which can be signed. -/
-- class Signable {A : Type} (t : Type) [DecidableEq t] :=
--   mkSignable : A → t
