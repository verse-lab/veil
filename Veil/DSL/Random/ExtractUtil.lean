import Veil.Std
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Nodup
import Loom.MonadAlgebras.Instances.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Bits
import Mathlib.Data.FinEnum

-- some commonly used things during extraction

instance Fin.pos_then_inhabited {n : Nat} (h : 0 < n) : Inhabited (Fin n) where
  default := Fin.mk 0 h

instance (n : Nat) : TotalOrder (Fin n) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega

instance (n : Nat) : TotalOrderWithMinimum (Fin n.succ) where
  le := fun x y => x.val ≤ y.val
  le_refl := by simp
  le_trans := by simp ; omega
  le_antisymm := by simp ; omega
  le_total := by simp ; omega

  lt := fun x y => x.val < y.val
  le_lt := by simp ; omega

  next x y := y.val = x.val.succ
  next_def := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ; simp only [Fin.mk.injEq]
    constructor
    · intro ; subst y ; refine And.intro (Nat.le_refl _) ?_
      rintro ⟨z, hz⟩ ; dsimp only [Fin.val] ; exact id
    · rintro ⟨h1, h2⟩
      rw [Nat.lt_succ_iff_lt_or_eq] at hx ; rcases hx with (hx | hx)
      · specialize h2 ⟨x.succ, Nat.succ_lt_succ hx⟩ (Nat.le_refl _) ; dsimp only [Fin.val] at h2
        exact Nat.eq_of_le_of_lt_succ h1 (Nat.lt_succ_of_le h2)
      · subst x ; have htmp := Nat.lt_of_le_of_lt h1 hy ; simp only [lt_self_iff_false] at htmp

  zero := 0
  zero_lt := by simp

/-- A rank-based ring topology, where each node is assigned with a unique `Nat` rank,
    nodes are sorted by their ranks, and the ring is formed by connecting the sorted
    list of nodes. -/
instance between_ring (node : Type) [DecidableEq node] (f : node → Nat)
  (h : ∀ n1 n2, n1 ≠ n2 → f n1 ≠ f n2) : Between node where
  btw := fun a b c => (f a < f b ∧ f b < f c) ∨ (f c < f a ∧ f a < f b) ∨ (f b < f c ∧ f c < f a)
  btw_ring := by aesop
  btw_trans := by omega
  btw_side := by omega
  btw_total := by
    intro a b c
    by_cases h1 : a = b ; subst_vars ; simp
    by_cases h2 : a = c ; subst_vars ; simp
    by_cases h3 : b = c ; subst_vars ; simp
    have hh1 := h _ _ h1 ; have hh2 := h _ _ h2 ; have hh3 := h _ _ h3
    omega

instance between_ring' (l : List Nat) (hnodup : List.Nodup l) : Between (Fin l.length) :=
  between_ring (Fin _) l.get (by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h1 ; simp at * ; rw [List.Nodup.getElem_inj_iff hnodup] ; assumption)

instance between_ring'' (n : Nat) (l : List Nat) (hlength : l.length = n) (hnodup : List.Nodup l) : Between (Fin n) := by
  have a := between_ring' l hnodup
  rw [hlength] at a ; exact a

-- NOTE: the original design is based on `Finset`, but the `Repr`
-- instance of `Finset` is marked as unsafe, so we use `List` instead
abbrev SimpleQuorum (n : Nat) : Type :=
  { fs : List (Fin n) // fs.Sorted (· < ·) ∧ (n / 2 + 1) ≤ fs.length }

instance (n : Nat) : Inhabited (SimpleQuorum n.succ) where
  default := ⟨List.ofFn id, by
    simp [StrictMono] ; constructor
    · rintro ⟨a, b⟩ ; simp [← Fin.val_fin_lt] ; omega
    · rw [← Nat.div2_val] ; rcases (Nat.even_or_odd' n) with ⟨k, (h | h)⟩ <;> subst n <;> simp <;> omega⟩

theorem Finset.List.ofFn_filter {n : Nat} (p : Finset (Fin n)) :
  letI l := List.ofFn (n := n) id |>.filter (fun i => i ∈ p)
  List.Sorted (· < ·) l ∧ l.length = p.card := by
  constructor
  · apply List.Pairwise.filter ; simp
  · induction p using Finset.induction_on with
    | empty => simp
    | insert a p hnotin ih =>
      simp [hnotin] ; have htmp : a ∈ List.ofFn (n := n) id := by simp
      rw [List.mem_iff_append] at htmp ; rcases htmp with ⟨l1, l2, htmp⟩ ; rw [htmp] at ih ⊢
      simp [List.filter] at ih ⊢ ; simp [decide_eq_false hnotin] at ih
      have htmp2 : List.Nodup (List.ofFn (n := n) id) := by apply List.Pairwise.nodup (r := (· < ·)) ; simp
      simp [htmp, List.nodup_middle, List.nodup_cons] at htmp2
      rw [← Nat.add_assoc, ← ih] ; congr! 3 <;> apply List.filter_congr <;> simp <;> aesop

def allSimpleQuorums (n : Nat) : List (SimpleQuorum n) :=
  let l := List.ofFn (n := n) id
  let res := FinEnum.Finset.enum l |>.filterMap (fun x =>
    if n / 2 + 1 ≤ x.card then .some (l.filter fun y => y ∈ x) else .none)
  res.attachWith _ (by
    intro x hmem ; unfold res l at hmem ; simp at hmem ; rcases hmem with ⟨fs, hcard, hmem⟩ ; subst x
    have ⟨h1, h2⟩ := Finset.List.ofFn_filter fs ; rw [h2] ; aesop)

instance (n : Nat) : FinEnum (SimpleQuorum n) :=
  FinEnum.ofList (allSimpleQuorums n)
    (by
      intro ⟨x, h1, h2⟩ ; dsimp [allSimpleQuorums] ; simp ; exists List.toFinset x
      have htmp := List.Pairwise.nodup h1 ; simp [List.toFinset_card_of_nodup htmp] ; refine And.intro h2 ?_
      apply List.Sorted.eq_of_mem_iff _ h1 ; simp ; apply List.Pairwise.filter ; simp)

open Lean Meta Elab Command in
/-- Given the name of an `enum` type defined in a `veil module`, generates
    the corresponding inductive type and proves that this inductive type
    is an instance of the underlying typeclass of that `enum` type. -/
def deriveEnumInstance (name : Name) : CommandElabM Unit := do
  let clsName ← resolveGlobalConstNoOverloadCore (name.appendAfter "_Enum")
  let .some info := getStructureInfo? (← getEnv) clsName | throwError "no such structure {clsName}"
  -- NOTE: assume the last two are the propositions to satisfy
  let fields := info.fieldNames.pop.pop
  let ctors : Array (TSyntax ``Lean.Parser.Command.ctor) ←
    fields.mapM fun fn => `(Lean.Parser.Command.ctor| | $(mkIdent fn):ident )
  trace[veil.debug] "fields: {fields}"
  let defineIndTypeCmd ← do
    if ctors.size > 0 then
      `(inductive $(mkIdent name) where $[$ctors]* deriving DecidableEq, Inhabited, Repr, Nonempty)
    else
      `(inductive $(mkIdent name) where deriving DecidableEq, Repr)
  trace[veil.debug] "defineIndTypeCmd: {defineIndTypeCmd}"
  let instClauses ←
    fields.mapM fun fn => `(Lean.Parser.Term.structInstField| $(mkIdent fn):ident := $(mkIdent <| name ++ fn):ident )
  let completeRequirement := info.fieldNames.back!
  let distinctRequirement := info.fieldNames.pop.back!
  let proof1 ← `(Lean.Parser.Term.structInstField| $(mkIdent distinctRequirement):ident := (by decide) )
  let proof2 ← do
    let x := mkIdent `x
    `(Lean.Parser.Term.structInstField| $(mkIdent completeRequirement):ident := (by intro $x:ident ; cases $x:ident <;> decide) )
  let instClauses := instClauses.push proof1 |>.push proof2
  let instantiateCmd ←
    `(instance : $(mkIdent clsName) $(mkIdent name) where $[$instClauses]*)
  trace[veil.debug] "instantiateCmd: {instantiateCmd}"
  elabCommand defineIndTypeCmd
  elabCommand instantiateCmd

elab "deriving_enum_instance_for " name:ident : command => do
  let name := name.getId
  deriveEnumInstance name

def DivM.run (a : DivM α) :=
  match a with
  | .res x => Option.some x
  | .div => Option.none
