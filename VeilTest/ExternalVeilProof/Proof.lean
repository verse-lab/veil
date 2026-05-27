import Veil
import VeilTest.ExternalVeilProof.Spec

namespace ExternalVeilProof

@[veil]
theorem keep_excluded (ρ σ node : Type) [node_dec_eq : DecidableEq node] [node_inhabited : Inhabited node]
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
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@keep.ext ρ σ node node_dec_eq node_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@Assumptions ρ node node_dec_eq node_inhabited ρ_sub)
      (@Invariants ρ σ node node_dec_eq node_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub)
      (@excluded ρ σ node node_dec_eq node_inhabited χ χ_rep χ_rep_lawful σ_sub ρ_sub) := by
  veil_solve_wp

end ExternalVeilProof
