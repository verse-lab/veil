module

public import Veil.Core.Tools.ModelChecker.Interface
public import LTLLib.LTL.Syntax

public section

namespace Veil.LivenessMC
open Lean

structure LivenessProperty (ρ σ : Type) where
  name : Name := Name.anonymous
  atoms: List (Veil.ModelChecker.SafetyProperty ρ σ)
  φ : LTLLib.Formula Nat -- Reference atomic props by their index in `atoms`

@[inline, specialize]
def LivenessProperty.sysLabel (p : LivenessProperty ρ σ) (th : ρ) (st : σ) : Std.HashSet Nat :=
  (p.atoms.foldl (init := ((0 : Nat), (∅ : Std.HashSet Nat))) fun (i, acc) a =>
    (i + 1, if a.holdsOn th st then acc.insert i else acc)).2

instance : Inhabited (LivenessProperty ρ σ) where
  default := {
    name := Name.anonymous
    atoms := []
    φ := default
  }
