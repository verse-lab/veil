module

public import Veil

/-! LSP regression: resuming the first module's proof must use its original
verification conditions after a later module has been elaborated.
Run `python3 scripts/tests/test-vc-manager-incrementality.py --multi-module`. -/

veil module VCManagerMultiModuleFirst

after_init { pure () }
action keep { pure () }
invariant [trivial] True
#gen_spec

@[veil]
theorem keep_trivial (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@keep.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@trivial ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  done

end VCManagerMultiModuleFirst

veil module VCManagerMultiModuleSecond

after_init { pure () }
action other { pure () }
invariant [later] True
#gen_spec

end VCManagerMultiModuleSecond

example := @VCManagerMultiModuleFirst.keep_trivial
