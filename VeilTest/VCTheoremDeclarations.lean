import Veil

veil module VCTheoremDeclarations

type node

relation r : node → Bool

#gen_state

after_init {
  r N := false
}

action keep {
  pure ()
}

invariant [excluded] r N ∨ ¬ r N

#gen_spec

#check_invariants

#gen_theorems

run_cmd do
  let expectedLocalNames := #[
    `initializer_doesNotThrow,
    `initializer_excluded,
    `initializer_excluded_tr,
    `keep_doesNotThrow,
    `keep_excluded,
    `keep_excluded_tr
  ]
  let mgr ← Veil.Verifier.vcManager.atomically fun ref => ref.get
  let actualLocalNames := (mgr.vcIdsInDependencyOrder Veil.VCMetadata.isInduction).filterMap fun vcId => do
    let vc ← mgr.nodes[vcId]?
    some vc.name
  unless actualLocalNames.size == expectedLocalNames.size do
    throwError "expected {expectedLocalNames.size} induction VCs, got {actualLocalNames.size}"
  for expected in expectedLocalNames do
    unless actualLocalNames.contains expected do
      throwError "expected induction VC `{expected}` to be registered"
  for actual in actualLocalNames do
    unless expectedLocalNames.contains actual do
      throwError "unexpected induction VC `{actual}` was registered"
  let env ← Lean.getEnv
  for localName in expectedLocalNames do
    let fullName := `VCTheoremDeclarations ++ localName
    unless (env.findConstVal? fullName).isSome do
      throwError "expected generated theorem declaration `{fullName}`"

end VCTheoremDeclarations

veil module VCTheoremDeclarationsReverseBridge

type node

relation r : node → Bool

#gen_state

after_init {
  r N := false
}

action keep {
  pure ()
}

invariant [excluded] r N ∨ ¬ r N

#gen_spec

@[veil]
theorem keep_excluded_tr (ρ σ node : Type) [node_dec_eq : DecidableEq node] [node_inhabited : Inhabited node]
    (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain node __veil_f) (State.Label.toCodomain node __veil_f)
          (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory node) ρ] :
    Veil.Transition.meetsSpecificationIfSuccessfulAssuming
      (@keep.ext.tr ρ σ node node_dec_eq node_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ node node_dec_eq node_inhabited ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@excluded ρ σ node node_dec_eq node_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  veil_solve_tr

#gen_theorems

run_cmd do
  let env ← Lean.getEnv
  for decl in #[
    `VCTheoremDeclarationsReverseBridge.keep_excluded,
    `VCTheoremDeclarationsReverseBridge.keep_excluded_tr
  ] do
    unless env.contains decl do
      throwError "expected theorem declaration `{decl}`"

end VCTheoremDeclarationsReverseBridge

veil module VCTheoremDeclarationNameConflict

type node

relation r : node → Bool

#gen_state

after_init {
  r N := false
}

action keep {
  pure ()
}

invariant [excluded] r N ∨ ¬ r N

#gen_spec

theorem keep_excluded : True := by
  trivial

#check_invariants

/--
error: cannot generate VC theorem `VCTheoremDeclarationNameConflict.keep_excluded` because a declaration with that name already exists with a different type
-/
#guard_msgs in
#gen_theorems

end VCTheoremDeclarationNameConflict

veil module VCTheoremDeclarationAlternativeNameConflict

type node

relation r : node → Bool

#gen_state

after_init {
  r N := false
}

action keep {
  pure ()
}

invariant [excluded] r N ∨ ¬ r N

#gen_spec

theorem keep_excluded_tr : True := by
  trivial

#check_invariants

/--
error: cannot generate VC theorem `VCTheoremDeclarationAlternativeNameConflict.keep_excluded_tr` because a declaration with that name already exists with a different type
-/
#guard_msgs in
#gen_theorems

end VCTheoremDeclarationAlternativeNameConflict
