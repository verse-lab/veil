import Veil.Frontend.DSL.Infra.State
import Veil.Frontend.DSL.Action.Semantics.Definitions
import Veil.Core.Tools.Checker.Concrete.DataStructure
import Veil.Frontend.DSL.Action.Extraction.Basic

open Veil

variable {ℂ ℝ 𝔸: Type}

def DivM.run (a : DivM α) :=
  match a with
  | .res x => Option.some x
  | .div => Option.none

def afterInit  {κᵣ ρ σᵣ : Type}
  (initVeilMultiExecM : VeilMultiExecM κᵣ ℤ ρ σᵣ Unit) (rd : ρ) (s₀ : σᵣ)
  : TsilT (ExceptT ℤ (PeDivM (List κᵣ))) (Unit × σᵣ) :=
  initVeilMultiExecM.run rd |>.run s₀

def nonDetNexts {κ κᵣ ρ σᵣ : Type}
  (mapVeilMultiExec : κ → VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)
  (r₀ : ρ) [IsSubReaderOf ℝ ρ]
  (s : σᵣ) [IsSubStateOf ℂ σᵣ] (l : κ) :=
  mapVeilMultiExec l r₀ s

/-- Extract the resulting state from an ExceptT-wrapped execution, if successful. -/
def getStateFromExceptT {ε α σ : Type}
  (c : ExceptT ε DivM (α × σ)) : Option σ :=
  match c.run with
  | DivM.res (Except.ok (_, st)) => some st
  | DivM.res (Except.error _)    => none
  | DivM.div
                 => none
def getAllStatesFromExceptT {ε α σ : Type}
  (c : List (ExceptT ε DivM (α × σ))) : List (Option σ) :=
  c.map getStateFromExceptT


inductive Freer (e : Type u → Type v) (α : Type w) where
  | pure : α → Freer e α
  | impure : ∀ {β : Type u}, e β → (β → Freer e α) → Freer e α

-- `semiOutParam`?
instance [MonadLiftT m e] : MonadLiftT m (Freer e) where
  monadLift x := Freer.impure (liftM x) Freer.pure

def Freer.bind {e : Type u → Type v} {α : Type w} {γ : Type y}
  (x : Freer e γ) (f : γ → Freer e α) : Freer e α :=
  match x with
  | .pure a => f a
  | .impure ex k => .impure ex fun b => (k b).bind f

instance : Monad (Freer e) where
  pure := Freer.pure
  bind := Freer.bind

instance : LawfulMonad (Freer e) :=
  LawfulMonad.mk' (Freer e)
  (id_map := by
    intro α x
    induction x with
    | pure a => rfl
    | impure ex k ih => simp [Functor.map, Freer.bind] ; ext b ; apply ih)
  (pure_bind := by intro α β a f ; rfl)
  (bind_assoc := by
    intro α β γ x f g
    induction x with
    | pure a => rfl
    | impure ex k ih => simp [bind, Freer.bind] ; ext b ; apply ih)

def Freer.fold (f : α → γ) (g : ∀ {β}, e β → (β → γ) → γ) : Freer e α → γ
  | .pure a => f a
  | .impure ex k => g ex fun b => Freer.fold f g (k b)

def Freer.unbox [inst : Monad m] [MonadLiftT e m] : Freer e α → m α :=
  Freer.fold inst.pure (inst.bind ∘ liftM)

abbrev BinopComp (op : β → β → β) (f g : α → β) : α → β :=
  fun x => op (f x) (g x)

infixr:65 "∔" => BinopComp Sum

instance (priority := high) [MonadLiftT m e] : MonadLiftT m (e ∔ f) where
  monadLift x := Sum.inl x

instance [MonadLiftT m f] : MonadLiftT m (e ∔ f) where
  monadLift x := Sum.inr x

inductive TimerEff : Type u → Type v where
  | start : TimerEff PUnit
  | record : TimerEff PUnit

def TimerEff.onPUnit : TimerEff β → β = PUnit
  | .start => rfl
  | .record => rfl

abbrev TimerT (e : Type u → Type v) (α : Type w) := Freer (e ∔ TimerEff) α

def handleTimerEff (useNs : Bool) (x : TimerEff β) : StateT Nat IO β :=
  let op := if useNs then IO.monoNanosNow else IO.monoMsNow
  let log n := IO.println ((s!"time elapsed: {n} ") ++ (if useNs then "ns" else "ms"))
  let rec go : TimerEff β → StateT Nat IO β
    | .start => do let now ← op ; set now
    | .record => do let past ← get ; let now ← op ; log (now - past) ; set now
  go x

def TimerT.run {e : Type → Type u} {α : Type}
  [inst : Monad e] [MonadLiftT (StateT Nat IO) e] (x : TimerT e α) (useNs : Bool := false) : e α :=
  x.fold inst.pure fun et f =>
    inst.bind (match et with | .inl e => e | .inr t => liftM (handleTimerEff useNs t)) f

def TimerT.purify {e : Type → Type u} {α : Type} [inst : Monad e] (x : TimerT e α) : e α :=
  x.fold inst.pure fun et f =>
    inst.bind (match et with | .inl e => e | .inr t => (by rw [t.onPUnit] ; exact (pure PUnit.unit))) f


def BFSAlgorithmx {κ κᵣ ρ σᵣ : Type}
  (st₀ : σᵣ) (rd : ρ)
  (labs : List κ)
  (mapVeilMultiExec : κ → VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)
  (INV : ρ → σᵣ → Prop)
  (restrictions : ρ → σᵣ → Bool)
  [∀rd : ρ, ∀st : σᵣ, Decidable (INV rd st)]
  [∀rd : ρ, ∀st : σᵣ, Decidable (restrictions rd st)]
  [Inhabited σᵣ] [Inhabited ρ] [Repr κ]
  [IsSubStateOf ℂ σᵣ] [IsSubReaderOf ℝ ρ]
  [Hashable σᵣ] [BEq σᵣ]
  : StateT (SearchContext σᵣ σᵣ) Id Unit := do
  CheckerM.addToSeen st₀
  -- CheckerM.addToSeen (hash st₀)
  CheckerM.enqueueState st₀
  let mut count := 1
  let mut search_continue := true
  while search_continue do
    let current_state_opt ← CheckerM.dequeueState
    match current_state_opt with
    | none =>
      dbg_trace "[BFS] explored all states, total {count}"
      -- search_continue := false
      return ()
    | some st =>
      -- let canMoveLabels := canMoveLabel rd st
      let canMoveLabels := labs
      for i in List.finRange canMoveLabels.length do
        match canMoveLabels[i]? with
        | none =>
          dbg_trace "[BFS] explored all states, total {count}"
          continue
        | some label =>
          let list_st'_opt := getAllStatesFromExceptT ((nonDetNexts mapVeilMultiExec rd st label).map Prod.snd)
          -- let mut print_flag := false
          for st'_opt in list_st'_opt do
            match st'_opt with
            | none => continue   -- divergence
            | some st' =>
              let already_seen ← CheckerM.wasSeen st'
              -- let already_seen ← CheckerM.wasSeen (hash st')
              if !already_seen then
                CheckerM.addToSeen st'
                CheckerM.addTransitionToLog st st' s!"{reprStr label}"
                if decide (INV rd st') then
                  if decide (restrictions rd st') then
                    CheckerM.enqueueState st'
                else
                  -- CheckerM.addCounterExample (hash st')
                  CheckerM.addCounterExample st'
                  search_continue := false
                  return ()

/-- Run BFS starting from `st₀` with reader `rd`, checking `INV` under `restrictions`. -/
def runModelCheckerx {κ κᵣ ρ σᵣ : Type}
  -- (st₀ : σᵣ)
  (rd : ρ)
  (labs : List κ)
  (initVeilMultiExecM : VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)
  (mapVeilMultiExec : κ → VeilMultiExecM κᵣ ℤ ρ σᵣ Unit)
  (INV : ρ → σᵣ → Prop)
  [∀rd : ρ, ∀st : σᵣ, Decidable (INV rd st)]
  [Inhabited σᵣ] [Inhabited ρ]
  [IsSubStateOf ℂ σᵣ] [IsSubReaderOf ℝ ρ]
  [BEq σᵣ] [Hashable σᵣ] [Repr κ]
  : Id (Unit × (SearchContext σᵣ σᵣ)) := do
  let cfg := SearchContext.empty
  let restrictions := (fun (_ : ρ) (_ : σᵣ) => true)
  let st₀ := (((afterInit initVeilMultiExecM rd default |>.map Prod.snd).map getStateFromExceptT)[0]!).getD default
  (BFSAlgorithmx st₀ rd labs mapVeilMultiExec INV restrictions).run cfg
