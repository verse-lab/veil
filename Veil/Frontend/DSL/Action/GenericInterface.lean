import Std
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ProxyType
import Mathlib.Tactic.CongrExclamation

namespace Attempt1

-- inductive FieldLabel
--   | leader
--   | pending

-- inductive AccessKind where
--   /-- e.g. `n` in `leader n` -/
--   | concrete (name : Lean.Name)
--   /-- e.g. `M` in `pending M n` -/
--   | quantified (name : Option Lean.Name)

-- inductive FieldAccess where
--   | leader (n : AccessKind)
--   | pending (m n : AccessKind)

-- def FieldType {node : Type} : FieldLabel → Type
--   | FieldLabel.leader => node → Bool
--   | FieldLabel.pending => node → node → Bool

-- def FieldType_concrete {node : Type} [BEq node] [Hashable node] : FieldLabel → Type
--   | FieldLabel.leader => Std.HashMap node Bool
--   | FieldLabel.pending => Std.HashMap (node × node) Bool

/-
"Getting the value from a field" and "getting the field from a
structure" should be seperate.

Usually, the modification to the field or the structure is done by
- getting a new field according to a description, and
- setting it back to the structure using `modifyGet`

So axiomatize each of these operations.
-/

class StateRepresentation (St : Type) (FieldLabel : Type) (fieldType : FieldLabel → Type) (fieldAccess : FieldLabel → Type u) (fieldTypeConcrete : FieldLabel → Type) where
  -- getting the field; should be trivial, once `St` is a structure
  getField : St → (f : FieldLabel) → fieldTypeConcrete f
  /-- Get the value of a field from the state.
      effectively, "exposing" the field itself as a function -/
  get : (f : FieldLabel) → fieldTypeConcrete f → fieldType f

  -- given a description, returns the modified field
  set : (f : FieldLabel)
    → fieldType f   -- still, the most generic description, is a function
    → fieldAccess f -- need this to tell which variables are ∀-quantified
    → fieldTypeConcrete f
    → fieldTypeConcrete f
  /-- Set the value of a field in the state. -/
  setField : St → (f : FieldLabel) → fieldTypeConcrete f → St

  -- change : (f : FieldLabel) → (oldVal : fieldType f) → (FieldAccess → fieldType f)

class LawfulStateRepresentation (St : Type) (FieldLabel : Type) (fieldType : FieldLabel → Type) (fieldAccess : FieldLabel → Type u) (fieldTypeConcrete : FieldLabel → Type)
  [inst : StateRepresentation St FieldLabel fieldType fieldAccess fieldTypeConcrete] where
  getField_setField_idempotent :
    ∀ (st : St) (f : FieldLabel) (fc : fieldTypeConcrete f),
      inst.getField (inst.setField st f fc) f = fc
  setField_setField_last :
    ∀ (st : St) (f : FieldLabel) (fc₁ fc₂ : fieldTypeConcrete f),
      inst.setField (inst.setField st f fc₁) f fc₂ = inst.setField st f fc₂
  setField_getField_idempotent :
    ∀ (st : St) (f : FieldLabel),
      inst.setField st f (inst.getField st f) = st
  combine : (f : FieldLabel) → (fa : fieldAccess f) → (v₁ v₂ : fieldType f) → fieldType f
  get_set_idempotent :
    ∀ (f : FieldLabel) (fc : fieldTypeConcrete f) (v : fieldType f) (fa : fieldAccess f),
      inst.get f (inst.set f v fa fc) =
        -- `v`: this is not correct
        -- ideally, what we want is something like: `combine v fa (inst.get f fc)`,
        -- where `combine` checks which variables are quantified in `fa`
        combine f fa v (inst.get f fc)
  set_set_last :
    ∀ (f : FieldLabel) (fc : fieldTypeConcrete f) (v₁ v₂ : fieldType f) (fa₁ fa₂ : fieldAccess f),
      inst.set f v₂ fa₂ (inst.set f v₁ fa₁ fc) = inst.set f v₂ fa₂ fc
  set_get_idempotent :
    ∀ (f : FieldLabel) (fc : fieldTypeConcrete f) (fa : fieldAccess f),
      inst.set f (inst.get f fc) fa fc = fc

inductive FieldLabel
  | leader
  | pending

-- NOTE: I don't think this would work at the object level ... we need concrete _terms_
-- inductive AccessKind where
--   /-- e.g. `n` in `leader n` -/
--   | concrete --(name : Lean.Name)
--   /-- e.g. `M` in `pending M n` -/
--   | quantified --(name : Option Lean.Name)

inductive FieldAccess (node : Type) : FieldLabel → Type 1 where
  | leader (n : Option node) : FieldAccess node FieldLabel.leader
  | pending (m n : Option node) : FieldAccess node FieldLabel.pending

def FieldType_FO (node : Type) : FieldLabel → Type
  | FieldLabel.leader => node → Bool
  | FieldLabel.pending => node → node → Bool

def FieldType_concrete (node : Type) [DecidableEq node] [Hashable node] : FieldLabel → Type
  | FieldLabel.leader => Std.HashMap node Bool
  | FieldLabel.pending => Std.HashMap (node × node) Bool

structure FOState (node : Type) where
  leader : node → Bool
  pending : node → node → Bool

structure FOState_concrete (node : Type) [DecidableEq node] [Hashable node] where
  leader : Std.HashMap node Bool
  pending : Std.HashMap (node × node) Bool

-- ok, here when `FieldAccess` is involved, things will get hairy
instance {node : Type} [DecidableEq node] [Hashable node] :
  StateRepresentation
  (FOState node)
  FieldLabel
  (FieldType_FO node)
  (FieldAccess node)
  (FieldType_FO node) where
  getField st f := match f with
    | FieldLabel.leader => st.leader
    | FieldLabel.pending => st.pending
  setField st f fc := match f, fc with
    | FieldLabel.leader, fc => { st with leader := fc }
    | FieldLabel.pending, fc => { st with pending := fc }
  -- the id case is trivial
  get _ fc := fc
  set f v fa fc := match f with
    | FieldLabel.leader =>
      (fun n =>
        match fa with
        | FieldAccess.leader m =>
          if (m.elim true (· = n)) then v n else fc n)
    | FieldLabel.pending =>
      (fun m n =>
        match fa with
        | FieldAccess.pending m' n' =>
          if (m'.elim true (· = m)) ∧ (n'.elim true (· = n)) then v m n else fc m n)

-- instance {node : Type} [DecidableEq node] [Hashable node] :
--   LawfulStateRepresentation
--   (FOState node)
--   FieldLabel
--   (FieldType_FO node)
--   (FieldAccess node)
--   (FieldType_FO node) where
--   getField_setField_idempotent := by
--     introv ; cases f <;> simp [StateRepresentation.getField, StateRepresentation.setField]
--   setField_setField_last := by
--     introv ; cases f <;> simp [StateRepresentation.setField]
--   setField_getField_idempotent := by
--     introv ; cases f <;> simp [StateRepresentation.setField, StateRepresentation.getField]
--   get_set_idempotent := by
--     introv ; cases f <;> simp [StateRepresentation.get, StateRepresentation.set]

-- unfortunately, since `combine` is not exposed, there is no way to get
-- a reasonable definition for `LawfulStateRepresentation`

-- something has to be fixed.

end Attempt1

namespace Attempt2

-- using a "reference" like method:
-- fixing `fieldType` to be relational (the __reference__ implementation),
-- and deriving it from some other datatype

/-
Three questions:
1. How to represent the interface? What are needed?
2. How to relate the canonical representation with the __equivalent__ one?
   What can we get? Can we avoid some metaprogramming here?
3. How to actually use the laws during verification?
-/

-- def factorial : Nat → Nat
--   | 0 => 1
--   | n+1 => (n+1) * factorial n
-- #print factorial
-- #print Nat.brecOn

abbrev ProdFromListType (ts : List Type) : Type :=
  ts.foldr Prod Unit

abbrev ArrowFromListType (base : Type) (ts : List Type) : Type :=
  ts.foldr (· → ·) base

def ArrowFromListType.apply {base : Type} {ts : List Type}
  (f : ArrowFromListType base ts) (args : ProdFromListType ts) : base :=
  match ts, f, args with
  | [], f, () => f
  | _ :: _, f, (x, xs) => ArrowFromListType.apply (f x) xs

#reduce (types := true) ProdFromListType [Nat, Bool, String]
#reduce (types := true) ArrowFromListType Bool [Nat, Bool, String]

-- NOTE: essentially currying
def lambdaTelescopeObjectLevel (base : Type) (ts : List Type)
  (k : (ProdFromListType ts) → base) : ArrowFromListType base ts :=
  match ts with
  | [] => k ()
  | t :: ts' =>
    fun (x : t) => lambdaTelescopeObjectLevel base ts' (fun xs => k (x, xs))

-- TODO these theorem names are distractive
theorem lambdaTelescopeObjectLevel.eta {base : Type} {ts : List Type}
  (a : ArrowFromListType base ts) :
  lambdaTelescopeObjectLevel base ts (fun args => a.apply args) = a := by
  induction ts with
  | nil => simp [lambdaTelescopeObjectLevel, ArrowFromListType.apply]
  | cons t ts ih =>
    simp [lambdaTelescopeObjectLevel, ArrowFromListType.apply]
    funext x ; specialize ih (a x) ; rw [ih]

theorem lambdaTelescopeObjectLevel.beta {base : Type} {ts : List Type}
  {k : (ProdFromListType ts) → base} (args : ProdFromListType ts) :
  (lambdaTelescopeObjectLevel base ts k).apply args = k args := by
  induction ts with
  | nil => simp [ProdFromListType] at k args ; simp [lambdaTelescopeObjectLevel, ArrowFromListType.apply]
  | cons t ts ih =>
    simp [ProdFromListType] at k args
    rcases args with ⟨a, args⟩
    simp [lambdaTelescopeObjectLevel, ArrowFromListType.apply]
    rw [ih]

def fieldAccess {FieldLabel : Type}
  (fieldComponents : FieldLabel → List Type)  -- HMM universe polymorphism? no?
  (f : FieldLabel) : Type := ProdFromListType <| List.map Option <| fieldComponents f

def chainedProdCmp (ts : List Type) (dec : ∀ ty ∈ ts, DecidableEq ty)
  (po : ProdFromListType (ts.map Option)) (p : ProdFromListType ts) : Bool :=
  match ts, po, p with
  | [], (), () => true
  | t :: ts', (o, po'), (x, p') =>
    (o.elim true (fun y => @decide (y = x) (dec t (by simp) _ _)))
    && chainedProdCmp ts' (fun ty h => dec ty (by simp ; exact (Or.inr h))) po' p'

def fieldAccessCmp {FieldLabel : Type}
  {fieldComponents : FieldLabel → List Type}
  {f : FieldLabel}
  (dec : ∀ ty ∈ fieldComponents f, DecidableEq ty)
  (fa : fieldAccess fieldComponents f)
  (rhs : ProdFromListType (fieldComponents f)) : Bool :=
  chainedProdCmp (fieldComponents f) dec fa rhs

def fieldType {FieldLabel : Type}
  (fieldComponents : FieldLabel → List Type)
  (f : FieldLabel) : Type := ArrowFromListType Bool (fieldComponents f)

abbrev rawField {FieldLabel : Type} (fieldComponents : FieldLabel → List Type)
  (l : FieldLabel) : Type := ArrowFromListType Bool (fieldComponents l)

abbrev rawStructure {FieldLabel : Type} (fieldComponents : FieldLabel → List Type) : Type :=
  ∀ l, rawField fieldComponents l

def combine {FieldLabel : Type}
  {fieldComponents : FieldLabel → List Type}
  -- TODO `dec` does not have to be this
  (dec : ∀ l, ∀ ty ∈ fieldComponents l, DecidableEq ty)
  {f : FieldLabel}
  (fa : fieldAccess fieldComponents f)
  (v₁ v₂ : fieldType fieldComponents f) : fieldType fieldComponents f :=
  lambdaTelescopeObjectLevel Bool (fieldComponents f) fun args =>
    if fieldAccessCmp (dec f) fa args then v₁.apply args else v₂.apply args

class StateRepresentation (St : Type u) {FieldLabel : Type}
  (fieldComponents : FieldLabel → List Type)
  (fieldTypeConcrete : FieldLabel → Type) where
  getField : St → (f : FieldLabel) → fieldTypeConcrete f
  get : (f : FieldLabel) → fieldTypeConcrete f → fieldType fieldComponents f

  set : (f : FieldLabel)
    → fieldType fieldComponents f
    → fieldAccess fieldComponents f
    → fieldTypeConcrete f
    → fieldTypeConcrete f
  setField : St → (f : FieldLabel) → fieldTypeConcrete f → St

class LawfulStateRepresentation (St : Type u) {FieldLabel : Type}
  (fieldComponents : FieldLabel → List Type)
  (dec : ∀ f, ∀ ty ∈ fieldComponents f, DecidableEq ty)
  (fieldTypeConcrete : FieldLabel → Type)
  (inst : StateRepresentation St fieldComponents fieldTypeConcrete) where
  getField_setField_idempotent :
    ∀ (st : St) (f : FieldLabel) (fc : fieldTypeConcrete f),
      inst.getField (inst.setField st f fc) f = fc
  setField_setField_last :
    ∀ (st : St) (f : FieldLabel) (fc₁ fc₂ : fieldTypeConcrete f),
      inst.setField (inst.setField st f fc₁) f fc₂ = inst.setField st f fc₂
  setField_getField_idempotent :
    ∀ (st : St) (f : FieldLabel),
      inst.setField st f (inst.getField st f) = st
  get_set_idempotent :
    ∀ (f : FieldLabel) (fc : fieldTypeConcrete f) (v : fieldType fieldComponents f)
      (fa : fieldAccess fieldComponents f),
      inst.get f (inst.set f v fa fc) = combine dec fa v (inst.get f fc)
  -- NOTE: this does not seem to make sense ...
  -- unfortunately, there does not seem to be a way to "pile up" the changes

  -- set_set_last :
  --   ∀ (f : FieldLabel) (fc : fieldTypeConcrete f) (v₁ v₂ : fieldType fieldComponents f)
  --     (fa₁ fa₂ : fieldAccess fieldComponents f),
  --     inst.set f v₂ fa₂ (inst.set f v₁ fa₁ fc) = inst.set f v₂ fa₂ fc
  -- set_set_squash :
  --   ∀ (f : FieldLabel) (fc : fieldTypeConcrete f) (v₁ v₂ : fieldType fieldComponents f)
  --     (fa₁ fa₂ : fieldAccess fieldComponents f),
  --     inst.set f v₂ fa₂ (inst.set f v₁ fa₁ fc) = inst.set f (combine dec fa₂ v₂ v₁) fa₁ fc
  set_get_idempotent :
    ∀ (f : FieldLabel) (fc : fieldTypeConcrete f) (fa : fieldAccess fieldComponents f),
      inst.set f (inst.get f fc) fa fc = fc

-- instance
--   (equiv : St ≃ St')
--   [inst : StateRepresentation St fieldComponents fieldTypeConcrete] :
--   StateRepresentation St' fieldComponents fieldTypeConcrete where

-- sanity check that these things at least work on FO representation of state

instance test {FieldLabel : Type}
  [DecidableEq FieldLabel]
  (fieldComponents : FieldLabel → List Type)
  (dec : ∀ l, ∀ ty ∈ fieldComponents l, DecidableEq ty) :
  StateRepresentation
  (rawStructure fieldComponents)
  fieldComponents
  (rawField fieldComponents) where
  getField st f := st f
  get _ fc := fc
  setField st f fc := fun l => if h : f = l then h ▸ fc else st l
  set _ v fa fc := combine dec fa v fc

-- instance
--   [DecidableEq FieldLabel]
--   (fieldComponents : FieldLabel → List Type)
--   (dec : ∀ l, ∀ ty ∈ fieldComponents l, DecidableEq ty) :
--   LawfulStateRepresentation
--   (rawStructure fieldComponents)
--   fieldComponents
--   dec
--   (rawField fieldComponents)
--   -- TODO why synthesis fails here?
--   (inst := test fieldComponents dec) where
--   getField_setField_idempotent := by
--     introv ; simp [StateRepresentation.getField, StateRepresentation.setField]
--   setField_setField_last := by
--     introv ; simp [StateRepresentation.setField]
--     funext f ; split <;> ((try subst_eqs) ; (try simp))
--   setField_getField_idempotent := by
--     introv ; simp [StateRepresentation.setField, StateRepresentation.getField]
--     funext f ; split <;> ((try subst_eqs) ; (try simp))
--   get_set_idempotent := by
--     introv ; simp [StateRepresentation.get, StateRepresentation.set]
--   set_get_idempotent := by
--     introv ; simp [StateRepresentation.set, StateRepresentation.get]
--     unfold combine ; simp [lambdaTelescopeObjectLevel.eta]
--   set_set_squash := by
--     introv ; simp [StateRepresentation.set]
--     unfold combine ; congr! 1 ; funext args
--     split_ifs with h1 h2

-- NOTE: an alternative approach that does not use piling up changes
-- is to allow multiple access patterns to correspond to the same field update.
-- in that case, squashing two updates into one is more or less straightforward.
-- however, that might introduce redundant checks in `if`.

namespace Attempt3

abbrev alternatives {FieldLabel : Type}
  (fieldComponents : FieldLabel → List Type)
  (f : FieldLabel) :=
  List (fieldAccess fieldComponents f × fieldType fieldComponents f)

def multiCombine {FieldLabel : Type}
  {fieldComponents : FieldLabel → List Type}
  {f : FieldLabel}
  (dec : ∀ ty ∈ fieldComponents f, DecidableEq ty)
  (favs : alternatives fieldComponents f)
  (vbase : fieldType fieldComponents f)
  (args : ProdFromListType (fieldComponents f)) : Bool :=
  favs.foldr (fun (fa, v) acc =>
    if fieldAccessCmp dec fa args then v.apply args else acc) (vbase.apply args)

  -- lambdaTelescopeObjectLevel Bool (fieldComponents f) fun args =>
  --   if fieldAccessCmp (dec f) fa args then v₁.apply args else v₂.apply args

class StateRepresentation (St : Type u) {FieldLabel : Type}
  (fieldComponents : FieldLabel → List Type)
  (fieldTypeConcrete : FieldLabel → Type) where
  getField : St → (f : FieldLabel) → fieldTypeConcrete f
  get : (f : FieldLabel) → fieldTypeConcrete f → fieldType fieldComponents f

  set : (f : FieldLabel)
    → (favs : alternatives fieldComponents f)
    → fieldTypeConcrete f
    → fieldTypeConcrete f
  setField : St → (f : FieldLabel) → fieldTypeConcrete f → St

class LawfulStateRepresentation (St : Type u) {FieldLabel : Type}
  (fieldComponents : FieldLabel → List Type)
  (fieldTypeConcrete : FieldLabel → Type)
  (inst : StateRepresentation St fieldComponents fieldTypeConcrete) where
  getField_setField_idempotent :
    ∀ (st : St) (f : FieldLabel) (fc : fieldTypeConcrete f),
      inst.getField (inst.setField st f fc) f = fc
  setField_setField_last :
    ∀ (st : St) (f : FieldLabel) (fc₁ fc₂ : fieldTypeConcrete f),
      inst.setField (inst.setField st f fc₁) f fc₂ = inst.setField st f fc₂
  setField_getField_idempotent :
    ∀ (st : St) (f : FieldLabel),
      inst.setField st f (inst.getField st f) = st

  get_set_idempotent :
    ∀ (f : FieldLabel)
      (dec : ∀ ty ∈ fieldComponents f, DecidableEq ty)
      (fc : fieldTypeConcrete f)
      (favs : alternatives fieldComponents f),
      inst.get f (inst.set f favs fc) =
        lambdaTelescopeObjectLevel Bool (fieldComponents f) (multiCombine dec favs (inst.get f fc))
  set_append :
    ∀ (f : FieldLabel) (fc : fieldTypeConcrete f)
      (favs₁ favs₂ : alternatives fieldComponents f),
      inst.set f favs₂ (inst.set f favs₁ fc) = inst.set f (favs₂ ++ favs₁) fc
  -- in this formalism, we __do not__ squash the sets; instead, we only __pile them up__.
  -- they should be cleared all at once when needed, by, e.g., using `get_set_idempotent`.
  -- set_squash :
  --   ∀ (f : FieldLabel)
  --     (dec : ∀ ty ∈ fieldComponents f, DecidableEq ty)
  --     (fc : fieldTypeConcrete f)
  --     (v : fieldType fieldComponents f)
  --     (fa : fieldAccess fieldComponents f)
  --     (favs : alternatives fieldComponents f),
  --     inst.set f ((fa, v) :: favs) fc = inst.set f (combine dec fa₂ v₂ v₁) fa₁ fc
  set_get_idempotent :
    ∀ (f : FieldLabel) (fc : fieldTypeConcrete f) (fa : fieldAccess fieldComponents f),
      inst.set f [(fa, inst.get f fc)] fc = fc

-- side question: is it possible to prove something about `StateRepresentation`,
-- by proving something about the canonical representation?
-- this seems to be related to the idea of parametricity?

instance canonicalRepresentation {FieldLabel : Type}
  [DecidableEq FieldLabel]
  (fieldComponents : FieldLabel → List Type)
  (dec : ∀ f, ∀ ty ∈ fieldComponents f, DecidableEq ty) :
  StateRepresentation
  (rawStructure fieldComponents)
  fieldComponents
  (rawField fieldComponents) where
  getField st f := st f
  get _ fc := fc
  setField st f fc := fun l => if h : f = l then h ▸ fc else st l
  set f favs fc := lambdaTelescopeObjectLevel Bool (fieldComponents f) (multiCombine (dec f) favs fc)

instance
  [DecidableEq FieldLabel]
  (fieldComponents : FieldLabel → List Type)
  (dec : ∀ f, ∀ ty ∈ fieldComponents f, DecidableEq ty) :
  LawfulStateRepresentation
  (rawStructure fieldComponents)
  fieldComponents
  (rawField fieldComponents)
  -- TODO why synthesis fails here?
  (inst := canonicalRepresentation fieldComponents dec) where
  getField_setField_idempotent := by
    introv ; simp [StateRepresentation.getField, StateRepresentation.setField]
  setField_setField_last := by
    introv ; simp [StateRepresentation.setField]
    funext f ; split <;> ((try subst_eqs) ; (try simp))
  setField_getField_idempotent := by
    introv ; simp [StateRepresentation.setField, StateRepresentation.getField]
    funext f ; split <;> ((try subst_eqs) ; (try simp))
  get_set_idempotent := by
    introv ; simp [StateRepresentation.get, StateRepresentation.set]
    congr ; funext a b c ; grind only   -- ?
  set_get_idempotent := by
    introv ; simp [StateRepresentation.set, StateRepresentation.get]
    unfold multiCombine ; simp [lambdaTelescopeObjectLevel.eta]
  set_append := by
    introv ; simp [StateRepresentation.set]
    unfold multiCombine ; simp [lambdaTelescopeObjectLevel.beta]

-- class RepresentationEquivCanonical
--   {FieldLabel : Type}
--   -- [DecidableEq FieldLabel]
--   (St : Type u)
--   (fieldComponents : FieldLabel → List Type)
--   -- (dec : ∀ f, ∀ ty ∈ fieldComponents f, DecidableEq ty)
--   (fieldTypeConcrete : FieldLabel → Type)
--   [inst : StateRepresentation St fieldComponents fieldTypeConcrete] where
--   st_equiv : St ≃ (rawStructure fieldComponents)
--   getField_eq :
--     ∀ (st : St) (f : FieldLabel),
--       letI a := inst.getField st f
--       a = sorry
      -- (canonicalRepresentation fieldComponents (fun f ty h => by
      --   cases h ; exact inferInstance) ).getField st f

-- instance
--   [DecidableEq FieldLabel]
--   (fieldComponents : FieldLabel → List Type)
--   (dec : ∀ f, ∀ ty ∈ fieldComponents f, DecidableEq ty) :
--   LawfulStateRepresentation
--   st
--   fieldComponents
--   fcType
--   -- TODO why synthesis fails here?
--   (inst := test fieldComponents dec) where

end Attempt3

end Attempt2
