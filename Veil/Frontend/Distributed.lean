module

public meta import Veil.Frontend.Distributed.Syntax
public meta import Veil.Frontend.Distributed.Elab

/-! # Distributed programs

A frontend that describes a system as the program each node runs, connected by
a network with chosen assumptions, and compiles it into an ordinary Veil
module. See `docs/Distributed-DSL.md`.
-/
