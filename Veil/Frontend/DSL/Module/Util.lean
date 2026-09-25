module

public meta import Veil.Frontend.DSL.Module.Util.Basic
public meta import Veil.Frontend.DSL.Module.Util.StateTheory
public meta import Veil.Frontend.DSL.Module.Util.Assertions
public meta import Veil.Frontend.DSL.Module.Util.AbstractState
public meta import Veil.Frontend.DSL.Module.Util.LocalRProp
public meta import Veil.Frontend.DSL.Module.Util.LocalTheoryProp
public meta import Veil.Frontend.DSL.Module.Util.Assemble
public meta import Veil.Frontend.DSL.Module.Util.ForModelChecker
public meta import Veil.Frontend.DSL.Module.Util.VeilDeclAttr

public meta section

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
-/
