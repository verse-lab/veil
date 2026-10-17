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

/-- Prompt the frontend to read the VCManager, e.g. to print the VCs. We use a
`Condvar` instead of `Channel` because channels on the frontend thread (which
is cancellable) are subject to potential race conditions. For instance,
multiple `#gen_spec`s can be running in parallel, and one of them will "eat"
the notification from a channel, which causes the other to wait forever. With a
`Condvar`, we can `notifyAll` and check the predicate/condition holds. -/
initialize frontendNotification : Std.Condvar ← Std.Condvar.new

/-- This is to ensure we don't keep spawning server processes when `#gen_spec`
is re-elaborated in the editor. -/
initialize vcServerStarted : Std.Mutex Bool ← Std.Mutex.new false

namespace Frontend

open Lean.Elab.Command in
def notify : CommandElabM Unit := do
  frontendNotification.notifyAll

end Frontend

end Veil
