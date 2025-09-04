import Lean
import Veil.Base
import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.Action.Syntax
import Veil.Frontend.DSL.Action.Semantics.Theorems
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Elaborators
import Veil.Frontend.DSL.Infra.Assertions
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Infra.Simp

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
