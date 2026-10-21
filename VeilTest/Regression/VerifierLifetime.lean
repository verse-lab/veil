module
meta import Veil.Frontend.DSL.Module.VCGen.Common
open Lean Elab Command Veil Veil.Verifier
meta section
private inductive ProbeKey where | first | second deriving BEq, Hashable, TypeName
private structure ProbeResult where
  owners : Nat
  deriving TypeName
private def await (label : String) (condition : BaseIO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← condition) do
    if (← IO.monoMsNow) > deadline then throw <| IO.userError s!"timeout: {label}"
    IO.sleep 1

private def makeAbandoned (dropSentinel : IO.Ref Bool) (mode : Nat)
    (origin : IO.CancelToken) : CommandElabM VCManagerEnvironment := do
  withReader (fun ctx : Command.Context => { ctx with cancelTk? := if mode == 4 then none else some origin }) do
    let before ← get
    if mode == 5 then modifyInfoState fun st => { st with enabled := false }
    let currentOrigin := (← read).cancelTk?
    runManager (if mode == 3 then currentOrigin else none)
    let owner ← getVCManagerOwner
    let decl ← liftTermElabM <| addVeilDefinition (Name.num `lifetimeAvailable mode) (mkConst ``True.intro) (compile := false)
    let env ← getEnv
    let detached := clearVerifierRuntime env
    unless (vcManagerExt.getState detached).isEmpty do throwError "top-level stripping failed"
    -- The original realization context is retained unchanged, and declaration
    -- lookup/realization continue to work in the worker's environment.
    let old : ProbeResult ← withEnv detached <| liftTermElabM <|
      Meta.realizeValue decl ProbeKey.first do
        unless (← getEnv).contains decl do throwError "realization lost local declaration"
        return { owners := (vcManagerExt.getState (← getEnv)).size }
    unless old.owners == 1 do throwError "fixture did not capture the owner through realization"
    let sentinel ← IO.CancelToken.new
    sentinel.onSet (dropSentinel.set true)
    let stmt : VCStatement := { name := `abandoned, params := #[], statement := ← `(True) }
    let id : DischargerIdentifier := { managerId := (← readVCManager)._managerId, vcId := 0, dischargerId := 0, name := `abandoned }
    let d ← Discharger.fromTermWith (← `(by exact $(mkIdent decl))) stmt id vcManagerCh fun _ data time => do
      discard <| sentinel.isSet
      match data with
      | .inl witness => return .proven (some witness) none time
      | .inr ex => return .error #[← safeExceptionEntry ex] time
    withVCManager fun ref => do
      let (mgr, _) := (← ref.get).addVC { stmt with metadata := default } {} #[d]
      ref.set (if mode == 2 then { mgr with dormantVCs := mgr.dormantVCs.insert 0 } else mgr)
    if mode != 0 then startAll
    unless !(← d.startTimePromise.isResolved) do throwError "abandoned worker started"
    -- Wrappers consume snapshot tasks while preserving the command info tree.
    modify fun st => { st with snapshotTasks := before.snapshotTasks }
    unless !(← owner.cancelTk.isSet) do throwError "consuming child snapshots canceled a live source"
    if mode != 3 then
      -- Lean also cancels this token for edits after the creating command.
      origin.set
      unless !(← owner.cancelTk.isSet) do throwError "later-command cancellation invalidated a live owner"
      unless (← readVCManager).nodes.size == 1 do throwError "live owner lost its VC"
    -- Abandon the source metadata too. A bare retained runtime is deliberately
    -- not lifetime authority: the callback must break historical-env cycles.
    modify fun st => { st with env := before.env, infoState := before.infoState }
    return owner

run_cmd do
  numCoresCache.set (some 0)
  try
    for mode in [0, 1, 2, 3, 4, 5] do
      let dropped ← IO.mkRef false
      let origin ← IO.CancelToken.new
      let owner ← makeAbandoned dropped mode origin
      await "source metadata finalizer" owner.cancelTk.isSet
      await "unstarted closure released" dropped.get
      if mode == 3 then
        -- Retaining an explicitly supplied cancellation handle must not keep
        -- abandoned source work alive. It is not a source-lifetime lease.
        unless !(← origin.isSet) do throwError "source cleanup set the caller's token"
      let mgr ← owner.manager.atomically fun ref => ref.get
      unless mgr.nodes.isEmpty do throwError "abandoned manager retained deferred closures"
      let rejected ← withEnv (vcManagerExt.setState (← getEnv) (({} : Std.HashMap Name VCManagerEnvironment).insert .anonymous owner)) do
        try
          withVCManager fun _ => pure ()
          pure false
        catch _ => pure true
      unless rejected do throwError "canceled owner accepted late frontend mutation"
      let active ← dispatcher.atomically fun ref => return (← ref.get).owners.size
      unless active == 0 do throwError "abandoned owner retained by dispatcher"
  finally
    numCoresCache.set none
  IO.println "unrequested, queued, dormant, supplied-token, standalone and metadata-disabled workers release retained environments: PASS"

run_cmd do
  runManager
  let owner ← getVCManagerOwner
  let decl ← liftTermElabM <| addVeilDefinition `lifetimeLive (mkConst ``True.intro) (compile := false)
  let stmt : VCStatement := { name := `live, params := #[], statement := ← `(True) }
  let id : DischargerIdentifier := { managerId := (← readVCManager)._managerId, vcId := 0, dischargerId := 0, name := `live }
  let d ← Discharger.fromTermWith (← `(by exact $(mkIdent decl))) stmt id vcManagerCh fun _ data time => do
    let realized : ProbeResult ← Meta.realizeValue decl ProbeKey.second do
      unless (← getEnv).contains decl do throwError "worker realization lost local declaration"
      return { owners := (vcManagerExt.getState (← getEnv)).size }
    unless realized.owners == 1 do throwError "worker realization semantics changed"
    match data with
    | .inl witness => return .proven (some witness) none time
    | .inr ex => return .error #[← safeExceptionEntry ex] time
  withVCManager fun ref => do
    let (mgr, _) := (← ref.get).addVC { stmt with metadata := default } {} #[d]
    ref.set mgr
  unless !(← owner.cancelTk.isSet) do throwError "live marker canceled queued owner"
  startAll
  await "live worker result" d.resultPromise.isResolved
  let some result := d.resultPromise.result?.get | throwError "missing live worker result"
  unless result.isSuccessful do
    match result with
    | .error errors _ => throwError "live realization failed: {errors.map (·.1.toMessageData)}"
    | _ => throwError "live worker failed"
  unless !(← owner.cancelTk.isSet) do throwError "live marker canceled finished owner"
  IO.println "live source metadata preserves queued work, local declaration elaboration and realization semantics: PASS"

-- The real wrapper waits for and consumes all child snapshot tasks. Its info
-- tree must continue owning the runtime for subsequent commands.
#guard_msgs in
run_cmd do
  runManager
  withVCManager fun ref => do
    let (mgr, _) := (← ref.get).addVC {
      name := `liveAcrossGuard, params := #[], statement := ← `(True), metadata := default } {}
    ref.set mgr

run_cmd do
  unless (← readVCManager).nodes.size == 1 do
    throwError "#guard_msgs discarded the live manager"
  withVCManager fun _ => pure ()
  IO.println "#guard_msgs preserves manager ownership for later commands: PASS"
