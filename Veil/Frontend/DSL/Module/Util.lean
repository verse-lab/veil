import Veil.Frontend.DSL.Module.Util.Basic
import Veil.Frontend.DSL.Module.Util.StateTheory
import Veil.Frontend.DSL.Module.Util.Assertions
import Veil.Frontend.DSL.Module.Util.AbstractState
import Veil.Frontend.DSL.Module.Util.LocalRProp
import Veil.Frontend.DSL.Module.Util.LocalTheoryProp
import Veil.Frontend.DSL.Module.Util.Assemble
import Veil.Frontend.DSL.Module.Util.ForModelChecker
import Veil.Frontend.DSL.Module.Util.VeilDeclAttr
import Veil.Frontend.DSL.Module.Util.VeilTerm

/-!
# Module Utilities

This file re-exports all the utility functions for Veil DSL modules.
The implementation is split across multiple files for better organization:

- `Util/Basic.lean`: Type instances, parameter utilities, and module accessors
- `Util/StateTheory.lean`: State and Theory structure declarations
- `Util/Assertions.lean`: Assertion elaboration and tactics
- `Util/LocalRProp.lean`: LocalRProp typeclass and locality proofs
- `Util/LocalTheoryProp.lean`: LocalTheoryProp typeclass and locality proofs
- `Util/Assemble.lean`: Definition registration and assembly functions
- `Util/ForModelChecker.lean`: Utilities for model checking
- `Util/VeilDeclAttr.lean`: Implementing the `veil_decl` attribute
- `Util/VeilTerm.lean`: Implementing the `veil_term%` elaborator and delaborator
-/
