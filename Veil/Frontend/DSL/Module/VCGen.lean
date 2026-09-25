module

public meta import Veil.Frontend.DSL.Module.VCGen.Common
public meta import Veil.Frontend.DSL.Module.VCGen.Induction
public meta import Veil.Frontend.DSL.Module.VCGen.Trace

public meta section

/-!
# VC Generation

This module re-exports all VC generation infrastructure:
- `Common`: Shared utilities for SMT result processing and discharger creation
- `Induction`: Inductive invariant preservation VCs
- `Trace`: Symbolic trace query VCs (`sat trace` / `unsat trace`)
-/
