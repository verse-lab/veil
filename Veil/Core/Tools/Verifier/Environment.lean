module

public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Frontend.DSL.Infra.Metadata
public meta import Veil.Core.Tools.Verifier.Manager

public meta section

open Lean
namespace Veil

/-- Runtime owned by a specification's environment checkpoint. -/
structure VCManagerEnvironment where
  manager : Std.Mutex (VCManager VCMetadata SmtResult)
  errors : IO.Ref (Array String)
  cancelTk : IO.CancelToken

/-- A channel for communicating with the VCManager. -/
initialize vcManagerCh : Std.Channel (ManagerNotification VCMetadata SmtResult) ← Std.Channel.new

/-- This is to ensure we don't keep spawning server processes when `#gen_spec`
is re-elaborated in the editor. -/
initialize vcServerStarted : Std.Mutex Bool ← Std.Mutex.new false

end Veil
