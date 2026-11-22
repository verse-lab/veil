module

public import Veil.Frontend.Std
public meta import Lean

/-!
# Framing the part of a collection left unchanged by an update

The five lemmas below factor each proof into the part covered by the old
invariant and a small obligation at the new element or written key. Their
proofs are compiled once. On a VC we instantiate one lemma and construct the
remaining proof directly. See `Frame.lean` for rule selection and the final
kernel check on the public WP goal.
-/

namespace Veil.Frame
public section

/-- Extend a universal clause by checking it once at the inserted element. -/
theorem keepInsert {α κ : Type} [TSet α κ] (s : κ) (a : α) (P : α → Prop)
    (old : ∀ m : {x : α // x ∈ s}, P m.val) (fresh : P a) :
    ∀ m : {x : α // x ∈ TSet.insert a s}, P m.val := by
  intro ⟨x, hx⟩
  by_cases h : x = a
  · exact h ▸ fresh
  · exact old ⟨x, (TSet.contains_insert_other x a s h).symm.trans hx⟩

/-- An old witness still belongs to the enlarged set and has the same value. -/
theorem keepExistsInsert {α κ : Type} [TSet α κ] (s : κ) (a : α) (P : α → Prop)
    (old : ∃ m : {x : α // x ∈ s}, P m.val) :
    ∃ m : {x : α // x ∈ TSet.insert a s}, P m.val := by
  obtain ⟨⟨x, hx⟩, hp⟩ := old
  by_cases h : x = a
  · subst x; exact ⟨⟨a, TSet.contains_insert_self a s⟩, hp⟩
  · exact ⟨⟨x, (TSet.contains_insert_other x a s h).trans hx⟩, hp⟩

/-- For a pair of members, the old clause handles old/old. The other two premises
cover a new member in either position, including new/new. -/
theorem keepInsertPair {α κ : Type} [TSet α κ] (s : κ) (a : α) (P : α → α → Prop)
    (old : ∀ m n : {x : α // x ∈ s}, P m.val n.val)
    (left : ∀ y, P a y) (right : ∀ x, P x a) :
    ∀ m n : {x : α // x ∈ TSet.insert a s}, P m.val n.val := by
  intro m n
  apply keepInsert s a (fun x => P x n.val) _ (left n.val) m
  intro x
  exact keepInsert s a (P x.val) (old x) (right x.val) n

/-- Transport a pointwise clause through one update. Only the written key needs
a new proof. Use the decision procedure from the extracted update in the conclusion. -/
theorem keepAtOne {α β : Type} (k : α) (dec : ∀ j, Decidable (k = j))
    (f : α → β) (v : β) (P : α → β → Prop)
    (old : ∀ j, P j (f j)) (hit : P k v) :
    ∀ j, P j (@ite β (k = j) (dec j) v (f j)) := by
  intro j
  by_cases h : k = j
  · subst j; rwa [ite_eq_left rfl]
  · rw [ite_eq_right h]; exact old j

/-- Two fields written at the same key share one case split. -/
theorem keepAtTwo {α β γ : Type} (k : α) (dec : ∀ j, Decidable (k = j))
    (f : α → β) (v : β) (g : α → γ) (w : γ) (P : α → β → γ → Prop)
    (old : ∀ j, P j (f j) (g j)) (hit : P k v w) :
    ∀ j, P j (@ite β (k = j) (dec j) v (f j)) (@ite γ (k = j) (dec j) w (g j)) := by
  intro j
  by_cases h : k = j
  · subst j; rwa [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right h]; exact old j

meta section
open Lean Meta

/-- Close a leaf by computation, or introduce a few binders to reach a
contradictory constructor equality. For example, an implication whose premise
equates a vote to an append message holds for any conclusion. Returning
`none` lets the caller decline without running a general proof tactic. -/
private def directProof? (goal : Expr) (remainingBinders := 10) : MetaM (Option Expr) := do
  let goal ← whnf goal
  if goal.isConstOf ``True then return some (mkConst ``True.intro)
  if let some (_, lhs, rhs) := goal.eq? then
    if (← whnf lhs) == (← whnf rhs) then return some (← mkEqRefl rhs)
  let .forallE name domain body bi := goal | return none
  let n+1 := remainingBinders | return none
  withLocalDecl name bi domain fun x => do
    let target := body.instantiate1 x
    if let some (_, lhs, rhs) := domain.eq? then
      let env ← getEnv
      let ctor? (e : Expr) : MetaM (Option ConstructorVal) := do
        let some name := (← whnf e).getAppFn.constName? | return none
        let some (.ctorInfo info) := env.find? name | return none
        return some info
      if let some left ← ctor? lhs then
        if let some right ← ctor? rhs then
          if left.induct == right.induct && left.name != right.name then
            return some (← mkLambdaFVars #[x] (← mkNoConfusion target x))
    let some proof ← directProof? target n | return none
    return some (← mkLambdaFVars #[x] proof)

/-! ## Quantification over a set after insertion -/

private structure Insertion where
  elemType : Expr
  setType : Expr
  instanceArg : Expr
  elem : Expr
  oldSet : Expr

/-- Recognize the elaborated domain `{x // x ∈ TSet.insert a s}`. The set can
be a projection from the explicit post-state record. Reduce only its head. -/
private def insertionDomain? (domain : Expr) : MetaM (Option Insertion) := do
  let_expr Subtype _ pred := domain | return none
  let .lam _ _ membership _ := pred | return none
  let_expr Membership.mem _ _ _ set x := membership | return none
  unless x == .bvar 0 do return none
  let set ← if set.isAppOf ``TSet.insert then pure set else whnf set
  let_expr TSet.insert α κ inst a s := set | return none
  return some ⟨α, κ, inst, a, s⟩

private def Insertion.applyLemma (ins : Insertion) (lemmaName : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst lemmaName) (#[ins.elemType, ins.setType, ins.instanceArg, ins.oldSet, ins.elem] ++ args)

/-- Turn a clause on a subtype member `m` into a predicate on its value.
The value is shared between the old and new sets. A reference to the
membership proof itself cannot be transported by these lemmas. -/
private def memberPredicate (elemType domain body : Expr) : MetaM Expr :=
  withLocalDeclD `m domain fun m => withLocalDeclD `x elemType fun x => do
    let val ← mkAppM ``Subtype.val #[m]
    let body := (body.instantiate1 m).replace fun e =>
      if e == val || e == .proj ``Subtype 0 m then some x else none
    if body.containsFVar m.fvarId! then throwError "clause depends on the membership proof"
    mkLambdaFVars #[x] body

/-- Supply the two new-member cases for `∀ x y ∈ s, P x y`. We require a
direct proof with the other element arbitrary. This keeps the number of
obligations fixed even when the surrounding invariant has more binders. -/
private def frameMemberPair (ins : Insertion) (domain pred old : Expr) : MetaM Expr := do
  let pairPred ← withLocalDeclD `x ins.elemType fun x => do
    mkLambdaFVars #[x] (← memberPredicate ins.elemType domain ((pred.beta #[x]).bindingBody!))
  let proofAt (first : Bool) := withLocalDeclD `other ins.elemType fun other => do
    let args := if first then #[ins.elem, other] else #[other, ins.elem]
    let some proof ← directProof? (pairPred.beta args) | throwError "new pair needs a proof"
    mkLambdaFVars #[other] proof
  return ins.applyLemma ``keepInsertPair #[pairPred, old, ← proofAt true, ← proofAt false]

/-- Reuse an existential witness, or check the new cases of a universal clause.
Up to two unchanged outer binders may precede the set quantifier. For example,
`∀ voter, ∃ message ∈ msgs, …` keeps its witness after a message is inserted. -/
def frameInsertion (old goal : Expr) (outerBinders := 2) : MetaM Expr := do
  let goal ← whnf goal
  if goal.isAppOfArity ``Exists 2 then
    let_expr Exists domain pred := goal | unreachable!
    let some ins ← insertionDomain? domain | throwError "expected an existential over an insertion"
    let .lam _ _ body _ := pred | throwError "expected an existential predicate"
    return ins.applyLemma ``keepExistsInsert #[← memberPredicate ins.elemType domain body, old]
  let .forallE name domain body bi := goal | throwError "expected a set quantifier"
  let .forallE _ oldDomain oldBody _ ← whnf (← inferType old) | throwError "expected a universal pre-state clause"
  if let some ins ← insertionDomain? domain then
    let pred ← memberPredicate ins.elemType domain body
    if let .forallE _ secondDomain .. := pred.bindingBody! then
      if secondDomain == domain then return ← frameMemberPair ins domain pred old
    -- A second use of the set inside P can change P even on old members.
    let oldPred ← memberPredicate ins.elemType oldDomain oldBody
    let oldSet ← whnf ins.oldSet
    if oldSet.isFVar && oldPred.containsFVar oldSet.fvarId! then
      throwError "clause also uses the updated set in its body"
    let some fresh ← directProof? (pred.beta #[ins.elem]) | throwError "inserted element needs a proof"
    return ins.applyLemma ``keepInsert #[pred, old, fresh]
  let n+1 := outerBinders | throwError "expected an insertion under at most two outer binders"
  unless ← isDefEq oldDomain domain do throwError "outer quantifier changed"
  withLocalDecl name bi domain fun x => do
    mkLambdaFVars #[x] (← frameInsertion (mkApp old x) (body.instantiate1 x) n)

/-! ## Pointwise clauses after writing a function at one key -/

private structure PointWrite where
  key : Expr
  decideEq : Expr
  valueType : Expr
  oldField : Expr
  newValue : Expr

/-- Read the WP's encoding of an updated field applied to the quantified index:
`(fun j => if k = j then value else field j) index`. The old branch identifies
the field whose occurrences we can abstract in the pre-state clause. -/
private def pointWrite? (read index : Expr) : MetaM (Option PointWrite) := do
  let_expr ite ty guard dec yes no := read.headBeta | return none
  let some (_, key, arg) := guard.eq? | return none
  unless arg == index && !key.containsFVar index.fvarId! && no.isApp && no.appArg! == index do return none
  let field ← whnf no.appFn!
  unless field.isFVar do return none
  return some ⟨key, ← mkLambdaFVars #[index] dec, ty, field, yes.replaceFVar index key⟩

/-- Collect distinct field updates observed at this index. Skip subterms
independent of the index and stop descending once a read has been recognized. -/
private def pointWrites (body index : Expr) : MetaM (Array PointWrite) := do
  let writes ← IO.mkRef (#[] : Array PointWrite)
  body.forEach' fun e => do
    if e.isApp && e.appArg! == index && e.getAppFn.isLambda then
      if let some write ← pointWrite? e index then
        let found ← writes.get
        unless found.any (·.oldField == write.oldField) do
          if found.size == 2 then throwError "more than two updated fields"
          writes.set (found.push write)
      return false
    return e.containsFVar index.fvarId!
  writes.get

/-- At the written key we accept a direct proof, reflexivity of Nat's order,
or an action guard whose type already is the obligation. -/
private def proveAtKey (goal : Expr) (guards : Array Expr) : MetaM Expr := do
  if let some proof ← directProof? goal then return proof
  let target ← whnf goal
  if target.isAppOfArity ``Nat.le 2 then
    let lhs := target.appFn!.appArg!
    if ← isDefEq lhs target.appArg! then return ← mkAppM ``Nat.le_refl #[lhs]
  for h in guards do
    let type ← whnf (← inferType h)
    if type.getAppFn == target.getAppFn && (← isDefEq type target) then return h
  throwError "updated key needs a proof"

/-- Abstract the field reads out of the old clause to obtain the pointwise
predicate P. Instantiate it at the new values for the hit case. The lemma
reuses `old` at every other key. Two observed writes must agree on their key. -/
def framePointUpdate (old goal : Expr) (guards : Array Expr) : MetaM Expr := do
  let .forallE _ domain body _ ← whnf goal | throwError "expected a pointwise clause"
  let .forallE _ oldDomain oldBody _ ← whnf (← inferType old) | throwError "expected a pointwise hypothesis"
  unless domain == oldDomain do throwError "index domain changed"
  withLocalDeclD `j domain fun j => do
    let writes ← pointWrites (body.instantiate1 j) j
    let clause := oldBody.instantiate1 j
    match writes with
    | #[w] =>
      let pred ← withLocalDeclD `v w.valueType fun v =>
        mkLambdaFVars #[j, v] (clause.replace fun e => if e == mkApp w.oldField j then some v else none)
      let hit ← proveAtKey (pred.beta #[w.key, w.newValue]) guards
      return mkAppN (mkConst ``keepAtOne) #[domain, w.valueType, w.key, w.decideEq, w.oldField, w.newValue, pred, old, hit]
    | #[w, u] =>
      unless w.key == u.key do throwError "fields updated at different keys"
      let pred ← withLocalDeclD `v w.valueType fun v => withLocalDeclD `z u.valueType fun z =>
        mkLambdaFVars #[j, v, z] (clause.replace fun e =>
          if e == mkApp w.oldField j then some v else if e == mkApp u.oldField j then some z else none)
      let hit ← proveAtKey (pred.beta #[w.key, w.newValue, u.newValue]) guards
      return mkAppN (mkConst ``keepAtTwo) #[domain, w.valueType, u.valueType, w.key, w.decideEq,
        w.oldField, w.newValue, u.oldField, u.newValue, pred, old, hit]
    | _ => throwError "expected a read at the updated index"

end
end
end Veil.Frame
