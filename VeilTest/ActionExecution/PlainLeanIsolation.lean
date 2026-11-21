module

public import Veil

/-!
Importing Veil must not alter parsing or execution of ordinary Lean `do`
blocks unless the Veil syntax scope has explicitly been opened.
-/

set_option linter.unusedVariables false

def ordinaryUnderscoreDependentIf (p : Prop) [Decidable p] : Id Nat := do
  if _ : p then
    return 1
  else
    return 2

#guard Id.run (ordinaryUnderscoreDependentIf True) == 1
#guard Id.run (ordinaryUnderscoreDependentIf False) == 2

def ordinaryDanglingElse (outer : Bool) (p : Prop) [Decidable p] : Id Nat := do
  if outer then
    if h : p then
      return 1
  else
    return 2
  return 3

#guard Id.run (ordinaryDanglingElse true False) == 3

def veil_let : Nat := 7
#guard veil_let == 7

abbrev ExId := Nat
#guard ((0 : ExId) - 1) == 0

abbrev distinct : Prop := False
#guard !decide distinct

def ordinaryIdentifiers : Nat := Id.run do
  let pick := 1
  let assume := 2
  let assert := 3
  let veil := 4
  let module := 5
  let only := 6
  return pick + assume + assert + veil + module + only

#guard ordinaryIdentifiers == 21

def modulo (beta delta uqc : Nat) : Nat := (beta%3) + (delta%3) + (uqc%3)
#guard modulo 4 4 4 == 3

def IgnoreExn : Nat := 1
#guard [IgnoreExn] == [1]

def TotalOrder : Nat := 8
#guard TotalOrder == 8

example {α : Type u} (f : α → α) : f = f := by simp

example (p : Nat → Fin 3 → Prop) (h : ∀ n i, p n i) :
    ∀ (n : Nat) (i : Fin 3), p n i ∧ True := by
  simp
  intro n i
  exact h n i

structure KeyWithPayload where
  key : Nat
  payload : Nat
deriving BEq

instance : Ord KeyWithPayload where
  compare a b := compare a.key b.key

#guard Std.TreeSet.ofList [KeyWithPayload.mk 1 2] compare ==
  Std.TreeSet.ofList [KeyWithPayload.mk 1 3] compare

example {n : Nat} (p : Fin n → Prop) [DecidablePred p] :
    decide (∀ i, p i) = @decide _ (Nat.decidableForallFin p) := rfl

structure WithoutSerialization where
  value : Nat

example : True := by
  fail_if_success have : Repr WithoutSerialization := inferInstance
  fail_if_success have : Lean.ToJson WithoutSerialization := inferInstance
  trivial

example : True := by
  fail_if_success have : Lasso.Formula Bool := [ltl| ∀ b : Bool, ⊤]
  trivial

def readCounted (value checks : IO.Ref Nat) : IO Nat := do
  checks.modify (· + 1)
  value.get

/-- info: (3, 4) -/
#guard_msgs in
#eval show IO (Nat × Nat) from do
  let value ← IO.mkRef 0
  let checks ← IO.mkRef 0
  while (← readCounted value checks) < 3 do
    value.modify (· + 1)
    if (← value.get) ≥ 10 then break
  return (← value.get, ← checks.get)

set_option maxRecDepth 321
set_option maxHeartbeats 987654
set_option synthInstance.maxSize 765

veil module Isolation
individual counter : Nat

example : Veil.ExId = Int := rfl

after_init { counter := 0 }
action step { counter := counter + 1 }
end Isolation

def ordinaryIdentifierAfterModule : Nat := Id.run do
  let veil_let := 8
  return veil_let

#guard ordinaryIdentifierAfterModule == 8

section
local instance : Lean.ToJson Nat := ⟨fun _ => .str "custom encoding"⟩
#guard (Lean.toJson (17 : Nat)).compress == "\"custom encoding\""
end

open Lean Elab Command in
run_cmd do
  let opts ← getOptions
  unless maxRecDepth.get opts == 321 && maxHeartbeats.get opts == 987654 &&
      Meta.synthInstance.maxSize.get opts == 765 do
    throwError "veil module changed the surrounding elaboration options"
