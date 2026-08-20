module

public import Veil.Core.Tools.ModelChecker.Interface
public import LTLLib.LTL.Syntax

public section

namespace Veil.LivenessMC
open Lean

structure LivenessProperty (ρ σ : Type) where
  name : Name := Name.anonymous
  atoms: List (Veil.ModelChecker.SafetyProperty ρ σ)
  /-- The LTL formula, with atoms referenced by `SafetyProperty.name.toString`. -/
  φ : LTLLib.Formula String

@[inline, specialize]
def LivenessProperty.sysLabel (p : LivenessProperty ρ σ) (th : ρ) (st : σ) : Std.HashSet String :=
  p.atoms.foldl (init := ∅) fun acc a =>
    if a.holdsOn th st then acc.insert a.name.toString else acc

instance : Inhabited (LivenessProperty ρ σ) where
  default := {
    name := Name.anonymous
    atoms := []
    φ := default
  }
