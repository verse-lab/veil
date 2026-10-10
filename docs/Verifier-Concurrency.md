# Verifier concurrency

The verifier has three different lifetimes: a document/module session, a
verification request, and a solver attempt. Treating any two of these as the
same lifetime caused the cancellation, stale-result, and capacity races.

## Logical results and physical tasks

The session mutex serializes registration, accepted results, dependency
invalidation, ownership changes, and scheduling. `_dischargerResults` is the
authority for advancing a condition's sequence of solvers and deciding whether
that sequence is exhausted. A result promise can change on another thread;
publishing it does not itself change the manager's logical state.

Workers publish a result before exiting. Reconciliation supports a missing
notification by reading the promise. If it observes an exited task after an
earlier unsuccessful promise read, it reads the promise again before declaring
the result missing. Otherwise, publication between those reads would turn a
valid result into an error, which duplicate suppression would make permanent.

Every accepted result identifies the session, condition, solver slot, and slot
revision. Replacing an attempt changes its identity before it can be scheduled.
Duplicate or displaced results cannot alter the replacement's state.
Completion accounting also remembers accepted attempt identities, so replaying
a dependent interactive proof after prerequisite recovery counts it only once.

A result and a worker slot have different lifetimes. A worker can publish and
continue cleaning up, or remain inside a solver call after cancellation. The
process-wide pool retains actual task handles until `IO.hasFinished` reports
their exit. It covers all live sessions, including work displaced by document
edits. Lock order is session mutex followed by pool mutex. Worker publication
does not take either lock.

## Request ownership

Executable demand comes from live result waiters and explicit standalone
starts. A standalone `startAll` or `startFiltered` owns the conditions it starts
until session cancellation or supersession; a temporary waiter does not own those starts.
Each scope includes prerequisites and fallback alternatives. Ownership and
scheduling use that same closure, recomputed against current registrations.
This also enables newly registered conditions needed by an existing waiter.

When the last owner leaves, the manager first reconciles published results,
then disables pending work and revokes started attempts without a committed
result. Revoked results are rejected immediately, including before a replacement
exists. They cannot become verification failures or wake fallback conditions.
Queued attempts keep their unused tokens and promises. A later request rebuilds
only revoked attempts with fresh tokens, promises, and revisions; earlier
committed outcomes remain available. Interactive proofs clear obsolete retry
markers. Old physical tasks retain their capacity until exit. A started custom
attempt without a factory gets a diagnostic when retried.

Validation and request publication share the session lock, so the driver cannot
observe demand from a request that startup will reject. Validation also precedes
startup's resource mutations. Request finalizers release ownership
on startup failure, interruption, and normal completion.

## Dependencies and editor generations

A dependency names a particular condition, including when that condition was
registered as a fallback. An explicitly required fallback is made runnable;
waiting for its primary is insufficient because primary success leaves an
ordinary fallback dormant. Runtime dormancy is recomputed from registration-time
dormancy, current primary outcomes, and currently required prerequisites. A
released request or invalidated primary cannot leave an obsolete wake-up behind.
Result filters do not themselves force dormant alternatives: a filter selecting
only an ordinary dormant fallback returns that dormant status. Built-in checks
select its primary too; dependencies explicitly requiring the fallback force it.

Withdrawing a successful prerequisite invalidates descendants transitively.
Their replaced attempts receive new revisions. Physically running displaced
tasks are retained until exit. A dependent's interactive theorem is blocked
until its prerequisites recover, then replayed. Aggregate completion is computed from committed
results; a running next solver is not an exhausted sequence.

Command environments retain immutable registration checkpoints. An editor edit
forks from the checkpoint belonging to that command, reconstructs automatic
attempts, and retains an interactive result only if its theorem declaration is
still present with the same value. All nodes are reconstructed before interactive
results are replayed in dependency order. Public theorem checks use the local
proof rather than the exported axiom view. The session binding is not scoped:
ending a Lean section or namespace must not discard its registration checkpoint.
Factory failures become terminal diagnostics without destroying the old session.

Superseding a binding does not cancel requests held by reused command snapshots.
Lean cancels discarded snapshots, whose request finalizers release ownership.
Standalone demand is dropped on supersession. Retained callbacks and widgets
continue observing their original session; later commands use the fork. They
cannot write results into a newer document generation. A solver inside an
uninterruptible FFI call still occupies its physical slot until it returns or
times out, so an edit cannot bypass the process-wide capacity limit.

Manager mutation callbacks and discharger factories must not wait for solver
completion or re-enter the same session: they execute under its mutex. Factories
construct unstarted attempts; the session driver owns automatic worker startup.

The `Verifier*` regression targets cover publication/reconciliation overlap,
sequential fallback scheduling, worker cleanup, cancellation and retry, shared
prerequisites, standalone ownership, late registration, dormant prerequisites,
session capacity, retained document snapshots, section boundaries, factory
failures, document generations, and dependency invalidation.

After `lake build VeilTest`, `python3 scripts/test-verifier-lsp.py` exercises the
actual Lean language server with two modules, edits below a cached `#gen_spec`,
module deletion, undo, and rapid changes. It waits for complete diagnostics for
each checked document version and requires the verification checks to succeed.
