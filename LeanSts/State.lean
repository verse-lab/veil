def updateFn [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  λ (x : α) => if x = a then b else f x

def updateFn2 [DecidableEq α] [DecidableEq β] (f : α → β → γ)  (a : α) (b : β) (c : γ) : α → β → γ :=
  λ (x : α) (y : β) => if x = a && y = b then c else f x y

notation f"[ " a " ↦ " b " ]" => updateFn f a b
notation f"[ " a " , " b " ↦ " c " ]" => updateFn2 f a b c

@[simp] theorem updateFn_unfold [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
  (f[a ↦ b]) x = if x = a then b else f x := by
  simp only [updateFn]

@[simp] theorem updateFn2_unfold  [DecidableEq α] [DecidableEq β] (f : α → β → γ)  (a : α) (b : β) (c : γ) :
  (f[a , b ↦ c]) x y = if x = a && y = b then c else f x y := by
  simp only [updateFn2]
