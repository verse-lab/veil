import Veil.Frontend.DSL.State.Types

open Veil IteratedProd

def IteratedProd.ofListM {m : Type → Type} [Monad m]
  {α : Type} {β : α → Type} (f : (a : α) → m (β a))
  : (as : List α) → m (IteratedProd (as.map β))
  | []      => pure ()
  | a :: as => do
    let b ← f a
    let bs ← ofListM f as
    pure (b, bs)

/-- Version of `ofListM` that provides membership proof to the callback function.
    This is useful when the callback needs to prove properties about list elements.
    We use this function to inject _proof_ in concurrent search algorithm. -/
def IteratedProd.ofListMWithMem {m : Type → Type} [Monad m]
  {α : Type} {β : α → Type} (as : List α) (f : (a : α) → a ∈ as → m (β a))
  : m (IteratedProd (as.map β)) :=
  match as with
  | [] => pure ()
  | a :: as' => do
    let b ← f a List.mem_cons_self
    let bs ← ofListMWithMem as' (fun a' h => f a' (List.mem_cons_of_mem a h))
    pure (b, bs)


def IteratedProd.mapM [Monad m] {ts : List α} {T₁ T₂ : α → Type}
  (f : ∀ {a : α}, T₁ a → m (T₂ a))
  (elements : IteratedProd (ts.map T₁)) : m (IteratedProd (ts.map T₂)) := do
  match ts, elements with
  | [], _ => pure ()
  | _ :: _, (lis, elements) =>
    let head ← f lis
    let tail ← IteratedProd.mapM f elements
    pure (head, tail)

def IteratedProd.foldl {ts : List α} {T₁ : α → Type}
  (init : β)
  (prod : ∀ {a : α}, β → T₁ a → β)
  (elements : IteratedProd (ts.map T₁)) : β :=
  match ts, elements with
  | [], _ => init
  | _ :: _, (lis, elements) =>
    let res := prod init lis
    IteratedProd.foldl res prod elements
