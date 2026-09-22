module

public import Veil.Core.Tools.ModelChecker.CompiledRuntime
public import Veil.Core.Tools.ModelChecker.Concrete.Checker
public import Veil.Core.Tools.ModelChecker.Simulation
public import Veil.Frontend.DSL.Action.Extract
public import Veil.Frontend.Std
-- Generated checks and counterexamples evaluate the standard instances,
-- including enumeration, orders, and JSON serializers, during elaboration.
public meta import Veil.Frontend.Std
public import Lean
public import Veil.Base
public meta import Veil.Frontend.DSL.Module.Syntax
public meta import Veil.Frontend.DSL.Action.Syntax
public import Veil.Frontend.DSL.Action.Semantics.Theorems
public meta import Veil.Frontend.DSL.Module.Representation
public meta import Veil.Frontend.DSL.Module.Elaborators.Verification
public meta import Veil.Frontend.DSL.Infra.Assertions
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Frontend.DSL.Infra.Simp
public meta import Veil.Frontend.DSL.Tactic
public import Veil.Frontend.DSL.State.Instances
public import Veil.Frontend.DSL.State.Repr
public meta import Veil.Core.Tools.ModelChecker.Symbolic.TraceLang
public meta import Veil.Core.Tools.Verifier.TheoremDischarger

public meta section


/-! # Veil DSL

This module contains the syntax for the Veil DSL, which for clarity, is
broken into two parts:

- a language for declaring Veil modules, i.e.:
  - background theory
  - the state type (FO structure)
  - the set of initial states
  - transitions, actions, and procedures
  - properties (invariants, safety, liveness, etc.)
- a sub-language for the imperative language of actions and procedures

-/
