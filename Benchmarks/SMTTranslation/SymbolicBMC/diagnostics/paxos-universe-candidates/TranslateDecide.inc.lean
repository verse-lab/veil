/- Trusted-query diagnostic candidate, not a validated backend change.
   Lean decide p denotes true exactly when p holds. Trusted SMT represents
   both Bool values and Prop formulas by SMT Bool, so its instance argument
   should not become a computational dependency. Proof reconstruction for
   this additional translator has not been established. Prepared, not run. -/

@[smt_translate]
meta def issue123TranslateDecide : Smt.Translator := fun e => do
  let_expr decide p _inst := e | return none
  Smt.Translator.applyTranslators? p
