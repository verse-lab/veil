import Lean.PrettyPrinter.Delaborator.Basic

section MonadDrop

/--
The class `MonadDrop m n` allows a computation in monad `m` to be run in monad `n`.
For example, a `MetaM` computation can be ran in `EIO Exception`,
which can then be ran as a task using `EIO.asTask`.
-/
class MonadDrop (m : Type → Type) (n : outParam <| Type → Type) where
  /-- Translates an action from monad `m` into monad `n`. -/
  dropM {α} : m α → m (n α)

export MonadDrop (dropM)

variable {m n : Type → Type} [Monad m] [MonadDrop m n]

instance : MonadDrop m m where
  dropM := pure

instance {ρ} : MonadDrop (ReaderT ρ m) n where
  dropM act := fun ctx => dropM (act ctx)

instance {σ} : MonadDrop (StateT σ m) n where
  dropM act := do liftM <| dropM <| act.run' (← get)

instance {ω σ} [MonadLiftT (ST ω) m] : MonadDrop (StateRefT' ω σ m) n where
  dropM act := do liftM <| dropM <| act.run' (← get)

end MonadDrop

instance : Lean.Server.RpcEncodable Unit where
  rpcEncode _ := pure .null
  rpcDecode _ := pure ()
