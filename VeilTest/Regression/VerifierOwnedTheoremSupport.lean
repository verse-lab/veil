module
public meta import Veil.Core.Tools.Verifier.Server
public meta section
open Lean Veil
initialize environments : IO.Ref (Array Environment) ← IO.mkRef #[]
initialize owners : IO.Ref (Array VCManagerEnvironment) ← IO.mkRef #[]
