def updateFn [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  λ (x : α) => if x = a then b else f x

def updateFn2 [DecidableEq α] [DecidableEq β] (f : α → β → γ)  (a : α) (b : β) (c : γ) : α → β → γ :=
  λ (x : α) (y : β) => if x = a && y = b then c else f x y

def updateFn3 [DecidableEq α] [DecidableEq β] [DecidableEq γ] (f : α → β → γ → δ)  (a : α) (b : β) (c : γ) (d : δ) : α → β → γ → δ :=
  λ (x : α) (y : β) (z : γ) => if x = a && y = b && z = c then d else f x y z

def updateFn4 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ] (f : α → β → γ → δ → ε)  (a : α) (b : β) (c : γ) (d : δ) (e : ε) : α → β → γ → δ → ε :=
  λ (x : α) (y : β) (z : γ) (w : δ) => if x = a && y = b && z = c && w = d then e else f x y z w

notation f"[ " a " ↦ " b " ]" => updateFn f a b
notation f"[ " a " , " b " ↦ " c " ]" => updateFn2 f a b c
notation f"[ " a " , " b " , " c " ↦ " d " ]" => updateFn3 f a b c d
notation f"[ " a " , " b " , " c " , " d " ↦ " e " ]" => updateFn4 f a b c d e

@[simp] theorem updateFn_unfold [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
  (f[a ↦ b]) x = if x = a then b else f x := by
  simp only [updateFn]

@[simp] theorem updateFn2_unfold  [DecidableEq α] [DecidableEq β] (f : α → β → γ)  (a : α) (b : β) (c : γ) :
  (f[a , b ↦ c]) x y = if x = a && y = b then c else f x y := by
  simp only [updateFn2]

@[simp] theorem updateFn3_unfold  [DecidableEq α] [DecidableEq β] [DecidableEq γ] (f : α → β → γ → δ)  (a : α) (b : β) (c : γ) (d : δ) :
  (f[a , b , c ↦ d]) x y z = if x = a && y = b && z = c then d else f x y z := by
  simp only [updateFn3]

@[simp] theorem updateFn4_unfold  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ] (f : α → β → γ → δ → ε)  (a : α) (b : β) (c : γ) (d : δ) (e : ε) :
  (f[a , b , c , d ↦ e]) x y z w = if x = a && y = b && z = c && w = d then e else f x y z w := by
  simp only [updateFn4]
