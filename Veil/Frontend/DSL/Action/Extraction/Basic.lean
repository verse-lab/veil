import Loom.MonadAlgebras.NonDetT'.ExtractList

namespace Veil

abbrev VeilMultiExecM κ ε ρ σ α :=
  ReaderT ρ (StateT σ (TsilT (ExceptT ε (PeDivM (List κ))))) α

end Veil

instance : FinEnum Bool := FinEnum.ofList [true, false] (by decide)
