module

public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Frontend.DSL.Infra.Metadata
public meta import Veil.Core.Tools.Verifier.Manager

public meta section

open Lean
namespace Veil

/-- Prompt the frontend to read the VCManager, e.g. to print the VCs. We use a
`Condvar` instead of `Channel` because channels on the frontend thread (which
is cancellable) are subject to potential race conditions. For instance,
multiple `#gen_spec`s can be running in parallel, and one of them will "eat"
the notification from a channel, which causes the other to wait forever. With a
`Condvar`, we can `notifyAll` and check the predicate/condition holds. -/
initialize frontendNotification : Std.Condvar ← Std.Condvar.new

namespace Frontend

open Lean.Elab.Command in
def notify : CommandElabM Unit := do
  frontendNotification.notifyAll

end Frontend

end Veil
