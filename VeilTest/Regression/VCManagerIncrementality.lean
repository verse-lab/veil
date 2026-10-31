module

public import Veil

/-! LSP regression: inserting and deleting the step proof must restore the
interactive witnesses from the current Lean environment. A stale manager used
to keep the deleted theorem, and premature cleanup used to erase the VCs.
Run `python3 scripts/tests/test-vc-manager-incrementality.py --vc-manager`. -/

veil module VCManagerIncrementality

individual x : Nat
after_init { x := 0 }
action step { require x < 10; x := x + 1 }
invariant [bounded] x ≤ 10

-- Make the manual proof the only successful witness for the step invariant.
set_option veil.solver "custom"
#gen_spec

@[veil]
theorem initializer_bounded (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@initializer.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (fun _ _ => True) (@bounded ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  done

-- BEGIN STEP PROOF
@[veil]
theorem step_bounded (ρ : Type) (σ : Type) (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain __veil_f) (State.Label.toCodomain __veil_f) (χ __veil_f)
          (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming (@step.ext ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ ρ_sub) (@Invariants ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@bounded ρ σ χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  grind
-- END STEP PROOF

#gen_theorems

end VCManagerIncrementality
