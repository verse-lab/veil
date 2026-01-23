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

def IteratedProd.reverseAux :
  ∀ {ts ts' : List Type}, IteratedProd ts → IteratedProd ts' → IteratedProd (ts.reverseAux ts')
  | [], _, _, acc => acc
  | t :: _, ts', (b, bs), acc => reverseAux (ts' := t :: ts') bs (b, acc)

@[expose]
def IteratedProd.reverse {ts : List Type} (ip : IteratedProd ts) : IteratedProd (ts.reverse) :=
  reverseAux (ts' := []) ip ()

/-- Version of `ofListM` that provides membership proof to the callback function.
    This is useful when the callback needs to prove properties about list elements.
    We use this function to inject _proof_ in concurrent search algorithm. -/
@[inline, expose]
def IteratedProd.ofListMWithMem {m : Type → Type} [Monad m]
  {α : Type} {β : α → Type} (as : List α) (f : (a : α) → a ∈ as → m (β a))
  : m (IteratedProd (as.map β)) :=
  let rec @[specialize] loop : ∀ {ts : List Type} (as' : List α), (∀ a ∈ as', a ∈ as) → IteratedProd ts → m (IteratedProd (ts.reverseAux <| as'.map β))
    | _, [], _, bs => pure <| IteratedProd.reverse bs
    | ts, a :: as', pf, bs => do
      let b ← f a (pf a (by simp))
      loop (ts := β a :: ts) as' (fun a ha => pf a (by simp ; right ; exact ha)) (b, bs)
  loop (ts := []) as (by simp) ()

@[inline, expose]
def IteratedProd.mapM [Monad m] {as : List α} {T₁ T₂ : α → Type}
  (f : ∀ {a : α}, T₁ a → m (T₂ a)) : IteratedProd (as.map T₁) → m (IteratedProd (as.map T₂)) :=
  let rec @[specialize] loop : ∀ {ts : List Type} (as' : List α), IteratedProd ts → IteratedProd (as'.map T₁) → m (IteratedProd (ts.reverseAux <| as'.map T₂))
    | _, [], acc, _ => pure <| IteratedProd.reverse acc
    | ts, a :: as', acc, (x, xs) => do
      let y ← f x
      loop (ts := T₂ a :: ts) as' (y, acc) xs
  loop (ts := []) as ()

def IteratedProd.foldl {ts : List α} {T₁ : α → Type}
  (init : β)
  (prod : ∀ {a : α}, β → T₁ a → β)
  (elements : IteratedProd (ts.map T₁)) : β :=
  match ts, elements with
  | [], _ => init
  | _ :: _, (lis, elements) =>
    let res := prod init lis
    IteratedProd.foldl res prod elements

/-- A thin wrapper around `IO.asTask` to produce an `IteratedProd` of `Task`s. -/
def IteratedProd.taskSplit {β : α → Type} [Monad m] [MonadLiftT BaseIO m] [MonadLiftT IO m]
  (as : List α) (f : (a : α) → a ∈ as → IO (β a)) : m (IteratedProd <| as.map fun a => (Task (Except IO.Error <| β a))) := do
  IteratedProd.ofListMWithMem (as := as) fun subArr h_subArr_in => IO.asTask (f subArr h_subArr_in)
