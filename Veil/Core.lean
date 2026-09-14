import Veil.Frontend.Std
import Veil.Frontend.DSL.Infra.VerificationDiagnostics
import Lean
import Veil.Base
import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.Action.Syntax
import Veil.Frontend.DSL.Action.Semantics.Theorems
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Elaborators.Core
import Veil.Frontend.DSL.Infra.Assertions
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Infra.Simp
import Veil.Frontend.DSL.Tactic.Core
import Veil.Frontend.DSL.State.Instances
import Veil.Frontend.DSL.State.Repr


/-! # Solver-free Veil DSL and explicit-state model checking

This entry point excludes SMT, VC generation, and the verification manager.
Use `import Veil` to add verification commands. See `docs/Veil-Core.md` for
the `coreOnly` Lake profile and native model-checker dependency isolation.

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
