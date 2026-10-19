/- Optional companion candidate. Include after importing Smt.Real (which
   supplies the Rat/Real embedding) and FixedNatSimproc.inc.lean's text.
   Not yet compiled or tested; no Rat failure was established by AWS. -/

namespace Issue123EmbeddingCandidate

meta def fixedAddRealIsFractionalLemma : Lean.Meta.Simp.Simproc :=
  contextualArrow Smt.Preprocess.Embedding.isFractional

end Issue123EmbeddingCandidate

attribute [-embedding] Smt.Preprocess.Embedding.add_real_is_fractional_lemma

simproc ↓ [embedding] issue123_fixed_add_real_is_fractional_lemma (_ → _) :=
  Issue123EmbeddingCandidate.fixedAddRealIsFractionalLemma
