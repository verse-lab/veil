import Veil

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
