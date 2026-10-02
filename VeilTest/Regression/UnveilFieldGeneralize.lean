module

public import Veil

/-! `unveil` used to be hard-wired to the `veil_wp` + `veil_concretize_wp`
route.  That route ends by `generalize`-ing every state field into a plain
variable, which is not type correct when a field update is guarded by a
condition mentioning the very field being generalized: the `Decidable`
instance for the guard still refers to the original field.

Here `setNextOfPred` guards a `next` update with `is_free P`, which unfolds to
`color P = blue`, and `allocate` then also writes to `color`.  Abstracting
`color` left the guard's `Decidable` instance behind and `unveil` failed with
"Tactic `generalize` failed: result is not type correct".

`unveil` now goes through the local bridge theorem (`veil_apply_local_wp`)
first, which exposes the fields directly and never needs the generalization. -/
veil module UnveilFieldGeneralize

type Ptr

enum Color = { blue, white }

immutable individual null_ptr : Ptr

function next (a : Ptr) : Ptr
function color (obj : Ptr) : Color

#gen_state

ghost relation is_free (ptr : Ptr) := color ptr = blue

after_init {
  color O := blue
  next O := null_ptr
}

procedure setNextOfPred (target : Ptr) (nxt : Ptr) {
  next P := if is_free P ∧ next P = target then nxt else next P
}

action allocate {
  let ptr : Ptr ← pick
  require is_free ptr

  setNextOfPred ptr (next ptr)
  color ptr := white
  next ptr := null_ptr
}

invariant [free_block_next_wellformed]
  ∀ ptr, is_free ptr ∧ next ptr ≠ null_ptr → is_free (next ptr)

#gen_spec

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (ρ : Type) (σ : Type) (Ptr : Type) [Ptr_dec_eq : DecidableEq.{1} Ptr]
    [Ptr_inhabited : Inhabited.{1} Ptr] (Color : Type) [Color_dec_eq : DecidableEq.{1} Color]
    [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Ptr Color __veil_f) (State.Label.toCodomain Ptr Color __veil_f)
          (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Ptr Color __veil_f)
          (State.Label.toCodomain Ptr Color __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Ptr Color) ρ] :
    Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
      (@allocate.ext ρ σ Ptr Ptr_dec_eq Ptr_inhabited Color Color_dec_eq Color_inhabited Color_Enum χ χ_rep χ_rep_lawful
        σ_sub ρ_sub)
      (@Assumptions ρ Ptr Ptr_dec_eq Ptr_inhabited Color Color_dec_eq Color_inhabited Color_Enum ρ_sub)
      (@Invariants ρ σ Ptr Ptr_dec_eq Ptr_inhabited Color Color_dec_eq Color_inhabited Color_Enum χ χ_rep χ_rep_lawful
        σ_sub ρ_sub)
      (@free_block_next_wellformed ρ σ Ptr Ptr_dec_eq Ptr_inhabited Color Color_dec_eq Color_inhabited Color_Enum χ
        χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  unveil
  sorry

end UnveilFieldGeneralize
