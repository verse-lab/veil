import Veil.Core
import Veil.Frontend.DSL.Module.Elaborators.Verification
import Veil.Frontend.DSL.Tactic
import Veil.Core.Tools.ModelChecker.Symbolic.TraceLang
import Veil.Core.Tools.Verifier.TheoremDischarger


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
