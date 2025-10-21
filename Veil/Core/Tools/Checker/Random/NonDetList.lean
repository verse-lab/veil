import Veil.DSL.Random.ExtractListBasic
import Veil.Theory.WP

namespace MultiExtract

abbrev VeilMultiExecM κ (ρ σ α : Type) := ρ → σ → List (List κ × DivM (Except ExId (α × σ)))

def NonDetT.extractGenList_VeilM {findable} {α : Type}
  (findOf : ∀ {τ : Type} (p : τ → Prop), ExtCandidates findable κ p → Unit → List τ)
  : (s : VeilM m ρ σ α) → (ex : ExtractNonDet (ExtCandidates findable κ) s) →
  VeilMultiExecM κ ρ σ α
  | .pure x, _ => fun _ s => [([], DivM.res (Except.ok (x, s)))]
  | .vis x f, .vis _ _ _ =>
    fun r s =>
      match x r s with
      | DivM.res (Except.ok (y, s')) =>
        extractGenList_VeilM findOf (f y) (by rename_i a ; exact a y) r s'
      -- the following two cannot be merged into one case, due to return type mismatch
      | DivM.div => [([], DivM.div)]
      | DivM.res (Except.error e) => [([], DivM.res (Except.error e))]
  | .pickCont _ p f, .pickSuchThat _ _ _ _ =>
    fun r s =>
      findOf p ‹_› () |>.flatMap fun x =>
        let tmp := extractGenList_VeilM findOf (f x) (by rename_i a ; exact a x) r s
        let x := ExtCandidates.rep _ _ (self := ‹_›) x
        tmp.map fun (ks, y) => (x :: ks, y)

def NonDetT.extractList_VeilM {α : Type} (κ : Type _) (s : VeilM m ρ σ α)
  (ex : ExtractNonDet (ExtCandidates Candidates κ) s := by extract_list_tactic) :
  VeilMultiExecM κ ρ σ α :=
  NonDetT.extractGenList_VeilM
    (fun {α} p c => @ExtCandidates.core Candidates κ α p c |>.find) s ex

end MultiExtract

deriving instance Repr for DivM

def test : VeilM .external Unit Nat Nat := do
  let a ← MonadNonDet.pickSuchThat (Fin 5) (fun x => x.val > 1)
  if a = 2 then
    let b ← MonadNonDet.pickSuchThat (Fin 5) (fun x => x.val < 4)
    set b.val
    pure (a.val + b.val)
  else
    pure a

open MultiExtract in
def test_extracted : VeilMultiExecM Std.Format Unit Nat Nat :=
  MultiExtract.NonDetT.extractList_VeilM _ test

-- TODO have no idea why printing the whole result does not work
#eval test_extracted () 0 |>.map Prod.fst
#eval test_extracted () 0 |>.map Prod.snd
