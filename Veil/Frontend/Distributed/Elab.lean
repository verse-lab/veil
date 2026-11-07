module

public meta import Lean
public meta import Veil.Base
public meta import Veil.Util.Meta
public meta import Veil.Frontend.DSL.Module.Syntax
public meta import Veil.Frontend.DSL.Action.Syntax
public meta import Veil.Frontend.DSL.Infra.EnvExtensions
public meta import Veil.Frontend.Distributed.Syntax
public meta import Lean.Meta.Tactic.TryThis

public meta section

open Lean Parser Elab Command Term

/-! # Distributed programs as Veil modules

The `network`, `message`, `var` and `program` commands describe a system as the
sequential program every node runs. `program` compiles it into an ordinary Veil
module, so every Veil tool (`#model_check`, `#check_invariants`, `sat trace`,
...) works on it unchanged.

## The translation

A node runs until it blocks. The places where it can block -- each `recv` and
`next_round` -- and the head of each loop are the program's *resume points*.
Every node has a program counter `pc : node → pc_label`, which holds the
resume point it is suspended at (`pc_start` before it starts, `pc_done` once
it has stopped), and each resume point becomes one Veil action, parameterised
by the node (and, for a `recv`, the sender and the message fields). The action
requires the node to be suspended there, and then runs the program from that
point up to the next resume point, where it sets the program counter and
`return`s. A run between two resume points is a single atomic step.

A `let` binding therefore only lives until the end of the step it is made in:
values that must survive a `recv` belong in a `var`. The compiler rejects
programs that use a binding after it has expired.

Loop heads are resume points so that every loop is a sequence of steps, never
a loop inside one step. To avoid spending a step on every loop iteration, the
action that reaches the end of a loop body runs the loop test, and the next
iteration up to its first resume point, itself; it only stops at the loop head
if it gets back there within the same step. So a loop head only gets an action
if some step can suspend there: a loop that blocks on every iteration, like
`repeat recv ...`, needs none.

## Locality

A node variable `x : T` becomes a field `x : node → T`, and the compiler
replaces each mention of `x` in the program by `x self`. A node program has no
way to name another node's copy, nor any other mutable state: the network and
scheduler state the compiler generates, and any mutable state the user
declares outside the program, are rejected inside `program`. Immutable state
(the background theory) is shared knowledge, and may be read freely. Nodes
interact only through `send`, `broadcast`, `recv` and `received`, and the
sender of a message is always the node that sent it.

## Networks

* `async`: each message kind `m (x : T)` becomes a channel
  `m_net : node → node → T → Bool` (or `→ Nat`, for `channels := multiset`),
  indexed by sender and receiver. `send` adds a message, a `recv` action
  removes the message it receives. With `loss := lossy`, an action `net_drop_m`
  may remove any message in flight.
* `sync`: a round consists of every running node taking its step, after which
  the action `net_next_round` delivers all messages of the round together.
  `m_out` holds the messages sent in the current round, and `m_in` the ones
  delivered at the end of the previous one, which `received` reads. With
  `loss := lossy`, `net_drop_m` may remove any message of the current round
  before it is delivered. `net_ready n` records that `n` has not yet taken its
  step in this round.
* `order := fifo` (`async` only): every message carries a sequence number of
  the generated sort `net_seq`, ordered by `net_seq_order :
  TotalOrderWithMinimum net_seq`. `net_seq_sent src dst` is the number the next
  message from `src` to `dst` gets, and `net_seq_recv src dst` the number `dst`
  expects next; a `recv` can only take that message. With `loss := lossy`, it
  can take any later one instead, and the messages it skips are lost. Sending
  needs a successor number, so a model check over `net_seq := Fin (k + 1)`
  bounds every channel to `k` messages.
* `faults := crash f`: `net_crash n` stops node `n` (`pc n := pc_crashed`), at
  most `f` times (`net_crashes` counts them). In a `sync` network, a node that
  crashes in a round (`net_crashing`) may lose any of its messages of that
  round, through `net_drop_m`.
* `faults := byzantine p`: the nodes satisfying `p` (by default, the generated
  theory relation `byz`) do not run the program; `net_byz_send_m` lets them
  send any message, at any time, but with their own identity as the sender.
* `complexity := true` counts the messages sent (`net_msgs` point-to-point
  messages, `net_bcasts` broadcasts) and, for `sync`, the rounds (`net_rounds`).

Modelling loss and faults in `sync` networks as small actions on the current
round's messages, rather than as one nondeterministic choice of what each round
delivers, keeps model checking feasible: choosing a whole delivery relation
means enumerating all its possible values.
-/

namespace Veil.Distributed

/-! ## Declarations -/

inductive Synchrony where
  | async
  | sync
deriving Inhabited, BEq

inductive Faults where
  | none
  /-- Nodes may crash, at most `bound` of them (if given). -/
  | crash (bound : Option Term)
  /-- The nodes satisfying `pred` are Byzantine; `none` means a generated
  theory relation `byz`. -/
  | byzantine (pred : Option Term)
deriving Inhabited

structure NetConfig where
  synchrony : Synchrony := .async
  lossy : Bool := false
  multiset : Bool := false
  fifo : Bool := false
  faults : Faults := .none
  complexity : Bool := false
deriving Inhabited

def NetConfig.crash (cfg : NetConfig) : Bool := cfg.faults matches .crash _
def NetConfig.byzantine (cfg : NetConfig) : Bool := cfg.faults matches .byzantine _

structure MessageKind where
  name : Name
  fields : Array (Ident × Term)
  ref : Syntax
deriving Inhabited

structure NodeVar where
  name : Name
  ty : Term
  /-- `none`: the type's default value; `some none`: an arbitrary value;
  `some (some e)`: the value of `e`. -/
  init : Option (Option Term)
  ref : Syntax
deriving Inhabited

/-- Everything declared for the distributed program of one Veil module. -/
structure Decls where
  config : Option NetConfig := none
  messages : Array MessageKind := #[]
  vars : Array NodeVar := #[]
  programDone : Bool := false
  /-- The `program` command, and the Veil commands it compiled to (for
  `#desugar_program`). -/
  program? : Option (Syntax × Array (TSyntax `command)) := none
deriving Inhabited

private initialize declsExt : EnvExtension (NameMap Decls) ← registerEnvExtension (pure {})

private def getDecls (mod : Name) : CommandElabM Decls :=
  return (declsExt.getState (← getEnv)).getD mod {}

private def modifyDecls (mod : Name) (f : Decls → Decls) : CommandElabM Unit :=
  modifyEnv (declsExt.modifyState · fun m => m.insert mod (f (m.getD mod {})))

private def currentModuleName (cmd : String) : CommandElabM Name :=
  return (← getCurrentModule (errMsg := m!"`{cmd}` can only be used inside a `veil module`")).name

/-- The declarations of the current module, which must have declared its
network, and not yet compiled its program. -/
private def openDecls (cmd : String) : CommandElabM (Name × Decls) := do
  let mod ← currentModuleName cmd
  let decls ← getDecls mod
  if decls.config.isNone then
    throwError "`{cmd}` requires a `network` declaration first"
  if decls.programDone then
    throwError "`{cmd}` must come before the `program`"
  return (mod, decls)

/-! ## Generated names -/

private def pcName : Name := `pc
private def pcType : Name := `pc_label
private def readyName : Name := `net_ready
private def msgsName : Name := `net_msgs
private def bcastsName : Name := `net_bcasts
private def roundsName : Name := `net_rounds
private def emptyName : Name := `net_empty
private def haltedName : Name := `halted
private def correctName : Name := `correct
private def crashedName : Name := `crashed
private def crashesName : Name := `net_crashes
private def crashingName : Name := `net_crashing
private def byzName : Name := `byz
private def seqTypeName : Name := `net_seq
private def seqOrderName : Name := `net_seq_order
private def seqSentName : Name := `net_seq_sent
private def seqRecvName : Name := `net_seq_recv

/-- `net_seq_order.f`: a member of the order on sequence numbers. -/
private def seqOrd (f : Name) : Ident := mkIdent (seqOrderName ++ f)

private def label (s : String) : Ident := mkIdent (Name.mkSimple ("pc_" ++ s))
private def startLabel := label "start"
private def doneLabel := label "done"
private def crashedLabel := label "crashed"
private def recvLabel (id : Nat) := label s!"recv{id}"
private def loopLabel (id : Nat) := label s!"loop{id}"
private def roundLabel (id : Nat) := label s!"round{id}"

private def netChan (k : Name) : Name := k.appendAfter "_net"
private def outChan (k : Name) : Name := k.appendAfter "_out"
private def inChan (k : Name) : Name := k.appendAfter "_in"

/-! ## Declaration commands -/

@[command_elab Veil.networkDeclaration]
def elabNetwork : CommandElab := fun stx => do
  let mod ← currentModuleName "network"
  if (← getDecls mod).config.isSome then
    throwError "the network of this module has already been declared"
  let mut cfg : NetConfig := {}
  let mut seen : NameSet := {}
  for opt in stx[1].getArgs do
    let key := opt[1]
    let val := opt[3]
    let arg? : Option Term := if opt[4].getNumArgs == 0 then none else some ⟨opt[4][0]⟩
    if seen.contains key.getId then
      throwErrorAt key "network option `{key.getId}` is given twice"
    seen := seen.insert key.getId
    let bad (expected : MessageData) : CommandElabM NetConfig :=
      throwErrorAt val m!"expected {expected}"
    if let some arg := arg? then
      unless key.getId == `faults && (val.getId == `crash || val.getId == `byzantine) do
        throwErrorAt arg "only `faults := crash` and `faults := byzantine` take an argument"
    cfg ← match key.getId, val.getId with
      | `synchrony, `async => pure { cfg with synchrony := .async }
      | `synchrony, `sync => pure { cfg with synchrony := .sync }
      | `synchrony, _ => bad "`async` or `sync`"
      | `loss, `reliable => pure { cfg with lossy := false }
      | `loss, `lossy => pure { cfg with lossy := true }
      | `loss, _ => bad "`reliable` or `lossy`"
      | `channels, `set => pure { cfg with multiset := false }
      | `channels, `multiset => pure { cfg with multiset := true }
      | `channels, _ => bad "`set` or `multiset`"
      | `complexity, `false => pure { cfg with complexity := false }
      | `complexity, `true => pure { cfg with complexity := true }
      | `complexity, _ => bad "`true` or `false`"
      | `order, `unordered => pure { cfg with fifo := false }
      | `order, `fifo => pure { cfg with fifo := true }
      | `order, _ => bad "`unordered` or `fifo`"
      | `faults, `none => pure { cfg with faults := .none }
      | `faults, `crash => pure { cfg with faults := .crash arg? }
      | `faults, `byzantine => pure { cfg with faults := .byzantine arg? }
      | `faults, _ => bad "`none`, `crash` or `byzantine`"
      | _, _ => throwErrorAt key
          "unknown network option `{key.getId}`; the options are `synchrony`, `loss`, `channels`, `order`, `faults` and `complexity`"
  if cfg.synchrony == .sync && cfg.multiset then
    throwErrorAt stx "`channels := multiset` only applies to asynchronous networks: a synchronous network delivers the messages of a round together, as a set"
  if cfg.synchrony == .sync && cfg.fifo then
    throwErrorAt stx "`order := fifo` only applies to asynchronous networks: a synchronous network delivers the messages of a round together"
  if cfg.fifo && cfg.multiset then
    throwErrorAt stx "`order := fifo` numbers every message, so identical messages never merge: use the default `channels := set`"
  modifyDecls mod ({ · with config := some cfg })
  elabVeilCommand (← `(open Veil.Distributed))

@[command_elab messageDeclaration]
def elabMessage : CommandElab := fun stx => do
  let (mod, decls) ← openDecls "message"
  let name := stx[1]
  unless name.getId.isAtomic do
    throwErrorAt name "message names cannot contain dots"
  if decls.messages.any (·.name == name.getId) then
    throwErrorAt name "message `{name.getId}` is already declared"
  let mut fields := #[]
  for b in stx[2].getArgs do
    unless b.isOfKind ``Lean.Parser.Term.explicitBinder && b[2].getNumArgs == 2 && b[3].getNumArgs == 0 do
      throwErrorAt b "message fields must be written `(name : type)`"
    for x in b[1].getArgs do
      unless x.isIdent do throwErrorAt x "message fields must be named"
      if fields.any (·.1.getId == x.getId) then
        throwErrorAt x "message `{name.getId}` already has a field `{x.getId}`"
      fields := fields.push ((⟨x⟩ : Ident), (⟨b[2][1]⟩ : Term))
  modifyDecls mod fun d => { d with messages := d.messages.push { name := name.getId, fields, ref := stx } }

@[command_elab varDeclaration]
def elabVar : CommandElab := fun stx => do
  let (mod, decls) ← openDecls "var"
  let name := stx[1]
  unless name.getId.isAtomic do
    throwErrorAt name "variable names cannot contain dots"
  if decls.vars.any (·.name == name.getId) then
    throwErrorAt name "variable `{name.getId}` is already declared"
  let init : Option (Option Term) :=
    if stx[4].getNumArgs == 0 then none
    else
      let v := stx[4][0][1]
      -- `"*" <|> term` wraps the `*` alternative in a `token.«*»` node
      let isStar := v.isToken "*" || (v.getKind == Name.mkStr `token "*")
      if isStar then some none else some (some ⟨v⟩)
  modifyDecls mod fun d => { d with vars := d.vars.push { name := name.getId, ty := ⟨stx[3]⟩, init, ref := stx } }

/-! ## Node programs -/

/-- A message pattern of a `recv`, with one action parameter per field. A field
written as a term rather than a name gets a fresh parameter, which must equal
the term (selective receive). -/
structure MsgPattern where
  kind : MessageKind
  args : Array (Ident × Option Term)
  src : Ident
  ref : Syntax
deriving Inhabited

def MsgPattern.binders (p : MsgPattern) : NameSet :=
  p.args.foldl (fun s (x, _) => s.insert x.getId) (NameSet.empty.insert p.src.getId)

/-- The statements of a node program. Every statement other than the ones
listed here is `plain`: it is executed as written (after the locality
rewriting). -/
inductive Stmt where
  | plain (s : Syntax)
  | send (msg dst : Syntax) (ref : Syntax)
  /-- `guard?`: the condition of `broadcast (m X) if c`, which sends every
  instance of the pattern variables that satisfies `c`. -/
  | broadcast (msg : Syntax) (guard? : Option Syntax) (ref : Syntax)
  /-- `continues`: the single-pattern form `recv p`, whose bindings scope over
  the rest of the block; otherwise each alternative has its own body. -/
  | recv (id : Nat) (arms : Array (MsgPattern × List Stmt)) (continues : Bool) (ref : Syntax)
  /-- `cond` is a raw `doIfCond`, e.g. `h : c`. -/
  | ite (cond : Syntax) (thn els : List Stmt) (ref : Syntax)
  | loop (id : Nat) (cond : Syntax) (body : List Stmt) (ref : Syntax)
  | halt (ref : Syntax)
  | nextRound (id : Nat) (ref : Syntax)

instance : Inhabited Stmt := ⟨.halt .missing⟩

/-- What happens when a block of statements has run to its end. -/
inductive Frame where
  /-- run the rest of the enclosing block -/
  | seq (rest : List Stmt)
  /-- go back to the head of loop `id` -/
  | loopEnd (id : Nat) (cond : Syntax) (body : List Stmt)
  /-- continue with the code after the inlined `if` this block is a branch of -/
  | fallthrough

instance : Inhabited Frame := ⟨.fallthrough⟩

/-- A resume point, with the program that runs from it: `body`, followed by
`frames`. `dead` are the `let`-bound names in scope there, which do not
survive the suspension. -/
inductive Resume where
  | recvArm (id armIdx : Nat) (pat : MsgPattern) (body : List Stmt) (frames : List Frame) (dead : NameSet)
  | loopHead (id : Nat) (cond : Syntax) (body : List Stmt) (frames : List Frame) (dead : NameSet)
  | round (id : Nat) (body : List Stmt) (frames : List Frame) (dead : NameSet)

instance : Inhabited Resume := ⟨.round 0 [] [] {}⟩

private def dslStatementKinds : List SyntaxNodeKind :=
  [``sendDo, ``broadcastDo, ``recvDo, ``recvArmsDo, ``haltDo, ``nextRoundDo]

private def doSeqElems (s : Syntax) : Array Syntax :=
  if s.isOfKind ``Lean.Parser.Term.doSeqBracketed then s[1].getArgs.map (·[0])
  else if s.isOfKind ``Lean.Parser.Term.doSeqIndent then s[0].getArgs.map (·[0])
  else #[]

private partial def stripParens (s : Syntax) : Syntax :=
  if s.isOfKind ``Lean.Parser.Term.paren then stripParens s[1] else s

/-- Split a message term `(kind a b)` into its kind and arguments. -/
private def splitMessage (msgs : Array MessageKind) (s : Syntax) : CommandElabM (MessageKind × Array Syntax) := do
  let s' := stripParens s
  let (fn, args) := if s'.isOfKind ``Lean.Parser.Term.app then (s'[0], s'[1].getArgs) else (s', #[])
  unless fn.isIdent do
    throwErrorAt s "expected a message, e.g. `(vote r v)`"
  let some k := msgs.find? (·.name == fn.getId)
    | throwErrorAt fn "unknown message kind `{fn.getId}`"
  unless args.size == k.fields.size do
    throwErrorAt s "message `{k.name}` has {k.fields.size} field(s), but {args.size} are given"
  return (k, args)

/-- A name for a generated parameter: `base`, unless that is taken. -/
private def freshName (taken : NameSet) (base : Name) : Name := Id.run do
  if !taken.contains base then return base
  let mut i := 1
  while taken.contains (base.appendAfter s!"_{i}") do i := i + 1
  return base.appendAfter s!"_{i}"

/-- Whether `n` names a constructor, e.g. `true` or an `enum` value. As in
Lean's own patterns, such an identifier in a message pattern is a value to
match, not a variable to bind. -/
private def isConstructor (n : Name) : CommandElabM Bool := do
  let env ← getEnv
  return (← resolveGlobalName n).any fun (c, fields) =>
    fields.isEmpty && (env.find? c matches some (.ctorInfo _))

private def parsePattern (msgs : Array MessageKind) (reserved : NameSet) (p : Syntax) :
    CommandElabM MsgPattern := do
  let (k, argStx) ← splitMessage msgs p[0]
  let isBinder (a : Syntax) : CommandElabM Bool := do
    return a.isIdent && !(← isConstructor a.getId)
  -- names the user binds, which generated parameters must avoid
  let mut taken := reserved
  for a in argStx do
    if ← isBinder a then
      if taken.contains a.getId && !reserved.contains a.getId then
        throwErrorAt a "`{a.getId}` is bound twice in this pattern"
      taken := taken.insert a.getId
  let src ← if p[1].getNumArgs == 0 then
      pure (mkIdent (freshName taken `sender))
    else pure (⟨p[1][1]⟩ : Ident)
  if taken.contains src.getId then
    throwErrorAt src "`{src.getId}` is bound twice in this pattern"
  taken := taken.insert src.getId
  let mut args := #[]
  for a in argStx, (f, _) in k.fields do
    if ← isBinder a then
      args := args.push ((⟨a⟩ : Ident), none)
    else
      let x := freshName taken f.getId
      taken := taken.insert x
      let sel := if a.isOfKind ``Lean.Parser.Term.hole then none else some (⟨a⟩ : Term)
      args := args.push (mkIdentFrom a x, sel)
  for (x, _) in args do
    if reserved.contains x.getId then
      throwErrorAt x "`{x.getId}` is a node variable (or the node itself), and cannot be bound by a pattern"
  return { kind := k, args, src, ref := p }

private structure ParseCtx where
  msgs : Array MessageKind
  /-- names patterns may not bind: the node variables and `self` -/
  reserved : NameSet

private abbrev ParseM := ReaderT ParseCtx (StateT Nat CommandElabM)

private def freshId : ParseM Nat := modifyGet fun n => (n + 1, n + 1)

mutual
private partial def parseSeq (s : Syntax) : ParseM (List Stmt) :=
  (doSeqElems s).toList.mapM parseElem

private partial def parseElem (e : Syntax) : ParseM Stmt := do
  let ctx ← read
  let k := e.getKind
  if k == ``sendDo then return .send e[1] e[3] e
  if k == ``broadcastDo then
    let guard? := if e[2].getNumArgs > 0 then some e[2][1] else none
    return .broadcast e[1] guard? e
  if k == ``recvDo then
    let id ← freshId
    return .recv id #[(← parsePattern ctx.msgs ctx.reserved e[1], [])] true e
  if k == ``recvArmsDo then
    let id ← freshId
    let arms ← e[1].getArgs.mapM fun arm => do
      return (← parsePattern ctx.msgs ctx.reserved arm[1], ← parseSeq arm[3])
    return .recv id arms false e
  if k == ``haltDo then return .halt e
  if k == ``nextRoundDo then return .nextRound (← freshId) e
  if k == ``Lean.Parser.Term.doReturn then
    unless e[1].getNumArgs == 0 do
      throwErrorAt e "a node program cannot return a value; use `halt` to stop the node"
    return .halt e
  if k == ``Lean.Parser.Term.doIf then
    -- `if c then t (else if c' then t')* (else e)?`
    let els ← if e[5].getNumArgs == 0 then pure [] else parseSeq e[5][1]
    let els ← e[4].getArgs.foldrM (init := els) fun ei acc => do
      return [Stmt.ite ei[1] (← parseSeq ei[3]) acc ei]
    return .ite e[1] (← parseSeq e[3]) els e
  if k == ``Lean.Parser.Term.doWhile then
    -- The body follows the optional loop invariant and decreasing clauses.
    return .loop (← freshId) e[1] (← parseSeq e.getArgs.back!) e
  if k == ``Lean.Parser.Term.doRepeat then
    let cond := mkNode ``Lean.Parser.Term.doIfProp #[mkNullNode, ← `(True)]
    return .loop (← freshId) cond (← parseSeq e.getArgs.back!) e
  if k == ``Lean.Parser.Term.doFor then
    throwErrorAt e "`for` loops are not supported in node programs; use `while`"
  if k == ``Lean.Parser.Term.doBreak || k == ``Lean.Parser.Term.doContinue then
    throwErrorAt e "`break` and `continue` are not supported in node programs"
  if let some inner := e.find? (fun s => dslStatementKinds.contains s.getKind) then
    throwErrorAt inner "this statement can only appear directly in the program, or inside `if`, `while`, `repeat` and `recv` alternatives"
  return .plain e
end

/-! ### Scopes -/

/-- The identifiers occurring in `stx`. -/
private partial def identsIn (stx : Syntax) : Array Name :=
  if stx.isIdent then #[stx.getId] else stx.getArgs.foldl (· ++ identsIn ·) #[]

/-- The local names a statement binds for the rest of its block (best effort:
`let`, `let mut`, `let ← `, and `let :|`). Names of global constants (e.g.
constructors in a pattern) are not bindings. -/
private def boundBy (e : Syntax) : CommandElabM NameSet := do
  let k := e.getKind
  let pat? : Option Syntax :=
    -- the declaration is the last argument (it is preceded by `let`, `mut`?
    -- and, in recent Lean versions, a `letConfig`)
    if k == ``Lean.Parser.Term.doLet then some e.getArgs.back![0][0]
    else if k == ``Lean.Parser.Term.doLetArrow then some e.getArgs.back![0]
    else if k == ``letPick then some e[1]
    else none
  let some pat := pat? | return {}
  let mut names : NameSet := {}
  for n in identsIn pat do
    if n.isAtomic && (← resolveGlobalName n).isEmpty then
      names := names.insert n
  return names

/-- The resume points of a program. `scope` is the set of `let`-bound names
in scope at the statements `stmts`. -/
private partial def collect (stmts : List Stmt) (frames : List Frame) (scope : NameSet) :
    StateT (Array Resume) CommandElabM Unit := do
  match stmts with
  | [] => pure ()
  | s :: rest =>
    let frames' := Frame.seq rest :: frames
    match s with
    | .plain e =>
      let bound ← boundBy e
      collect rest frames (bound.foldl (·.insert ·) scope)
    | .recv id arms continues _ =>
      if continues then
        let pat := arms[0]!.1
        modify (·.push (.recvArm id 0 pat rest frames scope))
        collect rest frames (pat.binders.foldl (·.insert ·) scope)
      else
        for h : i in [0:arms.size] do
          let (pat, body) := arms[i]
          modify (·.push (.recvArm id i pat body frames' scope))
          collect body frames' (pat.binders.foldl (·.insert ·) scope)
        collect rest frames scope
    | .ite _ thn els _ =>
      collect thn frames' scope
      collect els frames' scope
      collect rest frames scope
    | .loop id cond body _ =>
      modify (·.push (.loopHead id cond body frames' scope))
      collect body (.loopEnd id cond body :: frames') scope
      collect rest frames scope
    | .nextRound id _ =>
      modify (·.push (.round id rest frames scope))
      collect rest frames scope
    | _ => collect rest frames scope

/-! ### Code generation -/

private structure Ctx where
  cfg : NetConfig
  self : Ident
  nodeT : Term
  messages : Array MessageKind
  varNames : NameSet
  /-- The number of arguments of each node variable (`0` unless it is a function). -/
  varArity : NameMap Nat
  /-- Names a node program may not mention, with the reason. -/
  forbidden : NameMap MessageData

/-- Code generation records the loops whose head some step suspends at: only
those loop heads need a resume action. -/
private abbrev M := ReaderT Ctx (StateT (Array Nat) CommandElabM)

/-- Within one action: the names that may no longer be used (`dead`), and the
names the action has bound so far (`bound`), which go out of scope whenever the
action leaves the block they were bound in. -/
private structure Scope where
  dead : NameSet := {}
  bound : NameSet := {}

private def Scope.bind (sc : Scope) (ns : NameSet) : Scope :=
  { dead := ns.foldl (·.erase ·) sc.dead, bound := ns.foldl (·.insert ·) sc.bound }

/-- Leave the current block: everything bound in this action so far is out of
scope (it was bound in a block nested in the one we continue with). -/
private def Scope.exit (sc : Scope) : Scope :=
  { sc with dead := sc.bound.foldl (·.insert ·) sc.dead }

private def isSync : M Bool := return (← read).cfg.synchrony == .sync

/-- The names that binders inside `stx` (`fun`, `∀`, `∃`, ...) introduce
(best effort). -/
private partial def binderNames (stx : Syntax) : NameSet :=
  go stx {}
where
  binderKinds : List SyntaxNodeKind :=
    [``Lean.explicitBinders, ``Lean.bracketedExplicitBinders, ``Lean.unbracketedExplicitBinders,
     ``Lean.Parser.Term.explicitBinder, ``Lean.Parser.Term.implicitBinder,
     ``Lean.Parser.Term.strictImplicitBinder, ``Lean.Parser.Term.instBinder]
  go (s : Syntax) (acc : NameSet) : NameSet :=
    -- `fun x => _` and `∀ x, _` bind the identifiers of their first argument
    let binders? :=
      if s.isOfKind ``Lean.Parser.Term.basicFun then some s[0]
      else if s.isOfKind ``Lean.Parser.Term.forall then some s[1]
      else if binderKinds.contains s.getKind then some s
      else none
    let acc := match binders? with
      | some b => (identsIn b).foldl (·.insert ·) acc
      | none => acc
    s.getArgs.foldl (fun acc c => go c acc) acc

/-- Reject uses of expired `let` bindings in `stx`. Names that `stx` binds
itself (`bound`, or by a binder inside it) are fresh, not uses. -/
private def checkDead (sc : Scope) (stx : Syntax) (bound : NameSet := {}) : M Unit := do
  let fresh := bound.foldl (·.insert ·) (binderNames stx)
  if let some x := stx.find? (fun s => s.isIdent && sc.dead.contains s.getId && !fresh.contains s.getId) then
    throwErrorAt x m!"`{x.getId}` is not available here: it was bound before a blocking `recv`, \
      `next_round` or loop iteration, and a `let` binding only lives until the node blocks. \
      Store the value in a `var` to keep it across steps."

mutual
/-- Make user syntax refer to this node's copy of each node variable, and
check that it touches no other mutable state. -/
private partial def localize (stx : Syntax) : M Syntax := do
  let ctx ← read
  match stx with
  | .ident _ _ val _ =>
    if ctx.varNames.contains val then
      -- no parentheses needed: this is a syntax tree, not text (and the
      -- printer of `#desugar_program` adds them where the text needs them)
      return mkNode ``Lean.Parser.Term.app #[stx, mkNullNode #[ctx.self.raw]]
    if let some why := ctx.forbidden.get? val then
      throwErrorAt stx why
    if let root :: field :: more := val.components then
      if ctx.varNames.contains root then
        let proj := (field :: more).foldl (· ++ ·) .anonymous
        return ← `(($(mkIdentFrom stx root) $(ctx.self)).$(mkIdentFrom stx proj):ident)
    return stx
  | .node info kind args =>
    if kind == ``receivedTerm then
      return ← expandReceived stx
    if kind == ``Lean.Parser.Term.app && args[0]!.isIdent && ctx.varNames.contains args[0]!.getId then
      let x := args[0]!.getId
      if args[1]!.getNumArgs > ctx.varArity.getD x 0 then
        throwErrorAt stx m!"`{x}` takes {ctx.varArity.getD x 0} argument(s): it is this node's own \
          variable, and a node cannot read another node's copy (in a `program`, `{x}` means `{x} self`)"
      let args' ← args[1]!.getArgs.mapM localize
      return .node info kind #[args[0]!, mkNullNode (#[ctx.self.raw] ++ args')]
    if kind == ``havocAssignment then
      -- `x := *` for a node variable `x` becomes `x self := *`
      return .node info kind (← args.mapM fun a =>
        if a.isIdent && ctx.varNames.contains a.getId then
          pure (mkNode ``Lean.Parser.Term.app #[a, mkNullNode #[ctx.self.raw]] : Syntax)
        else localize a)
    if kind == ``Lean.Parser.Term.doReassign then
      -- `x := e` for a node variable `x` becomes `x self := e`
      let d := args[0]!
      let x := if d[0].isIdent then d[0] else d[0][0]
      if (d.isOfKind ``Lean.Parser.Term.letIdDeclNoBinders || d.isOfKind ``Lean.Parser.Term.letIdDecl)
          && x.isIdent && ctx.varNames.contains x.getId && d[1].getNumArgs == 0 && d[2].getNumArgs == 0 then
        let lhs : Term := ⟨mkNode ``Lean.Parser.Term.app #[x, mkNullNode #[ctx.self.raw]]⟩
        let rhs : Term := ⟨← localize d[d.getNumArgs - 1]⟩
        return ← `(doElem| $lhs:term := $rhs)
    return .node info kind (← args.mapM localize)
  | _ => return stx

private partial def expandReceived (stx : Syntax) : M Syntax := do
  let ctx ← read
  unless ctx.cfg.synchrony == .sync do
    throwErrorAt stx "`received` is only available in synchronous networks; in an asynchronous network, use `recv`"
  let (k, args) ← splitMessage ctx.messages stx[1]
  let args : Array Term ← args.mapM fun a => return ⟨← localize a⟩
  let ch := mkIdent (inChan k.name)
  if stx[2].getNumArgs == 0 then
    let src := mkIdent `net_src
    `((∃ $src:ident, $ch $src $(ctx.self) $args* = true))
  else
    let src : Term := ⟨← localize stx[2][1]⟩
    `(($ch $src $(ctx.self) $args* = true))
end

private def userTerm (sc : Scope) (stx : Syntax) : M Term := do
  checkDead sc stx
  return ⟨← localize stx⟩

private def mkSeq (elems : Array Syntax) : M (TSyntax ``Lean.Parser.Term.doSeq) := do
  let elems ← if elems.isEmpty then pure #[(← `(doElem| pure ())).raw] else pure elems
  return ⟨mkNode ``Lean.Parser.Term.doSeqIndent
    #[mkNullNode (elems.map fun e => mkNode ``Lean.Parser.Term.doSeqItem #[e, mkNullNode])]⟩

private def mkIf (cond : Syntax) (thn : Array Syntax) (els : Option (Array Syntax)) : M Syntax := do
  let elsPart ← match els with
    | none => pure mkNullNode
    | some e => pure (mkNullNode #[mkAtom "else", ← mkSeq e])
  return mkNode ``Lean.Parser.Term.doIf #[mkAtom "if", cond, mkAtom "then", ← mkSeq thn, mkNullNode, elsPart]

/-- The statement `lhs := rhs`. -/
private def assign (lhs rhs : Term) : M Syntax := do
  return (← `(doElem| $lhs:term := $rhs)).raw

/-- Suspend this node at `lbl`, ending the step. `blocks`: the node waits for
the round to end (or has stopped), rather than being able to continue. -/
private def suspendAt (lbl : Ident) (blocks : Bool) : M (Array Syntax) := do
  let self := (← read).self
  let mut code := #[← assign (← `($(mkIdent pcName) $self)) lbl]
  if blocks && (← isSync) then
    code := code.push (← assign (← `($(mkIdent readyName) $self)) (← `(false)))
  return code.push (← `(doElem| return))

private def requireAt (lbl : Ident) : M (Array Syntax) := do
  let self := (← read).self
  let mut code := #[(← `(doElem| require $(mkIdent pcName):ident $self = $lbl)).raw]
  if (← isSync) then
    code := code.push (← `(doElem| require $(mkIdent readyName):ident $self))
  return code

private def countMessage (counter : Name) : M (Array Syntax) := do
  unless (← read).cfg.complexity do return #[]
  let c := mkIdent counter
  return #[← `(doElem| $c:ident := $c + 1)]

/-- The predicate that tells which nodes are Byzantine. -/
private def byzPred (cfg : NetConfig) : Option Term :=
  match cfg.faults with
  | .byzantine (some p) => some p
  | .byzantine none => some (mkIdent byzName)
  | _ => none

/-- `n` takes part in the protocol: it has neither stopped nor crashed, and it
is not Byzantine. -/
private def running (cfg : NetConfig) (n : Term) : CommandElabM Term := do
  let pc := mkIdent pcName
  let mut conds : Array Term := #[← `($pc $n ≠ $doneLabel)]
  if cfg.crash then conds := conds.push (← `($pc $n ≠ $crashedLabel))
  if let some p := byzPred cfg then conds := conds.push (← `(¬ $p $n))
  conds[1:].foldlM (fun acc c => `($acc ∧ $c)) conds[0]!

private def sendCode (sc : Scope) (msg : Syntax) (dst? : Option Syntax)
    (guard? : Option Syntax := none) : M (Array Syntax) := do
  let ctx ← read
  let (k, args) ← splitMessage ctx.messages msg
  let args ← args.mapM (userTerm sc)
  let guard? ← guard?.mapM (userTerm sc)
  if guard?.isSome && ctx.cfg.fifo then
    throwErrorAt msg "a guarded `broadcast` is not supported with `order := fifo`"
  let self := ctx.self
  let allDst := mkIdent `DST
  let dst ← match dst? with
    | some d => userTerm sc d
    | none => pure allDst
  let count ← countMessage (if dst?.isSome then msgsName else bcastsName)
  if ctx.cfg.fifo then
    -- the message gets the channel's next sequence number
    let ch := mkIdent (netChan k.name)
    let sent := mkIdent seqSentName
    let nxt := mkIdent `net_seq_next
    if dst?.isSome then
      let cur ← `($sent $self $dst)
      return #[(← `(doElem| let $nxt:ident :| $(seqOrd `next) $cur $nxt)).raw,
        ← assign (← `($ch $self $dst $cur $args*)) (← `(true)),
        ← assign cur nxt] ++ count
    else
      let seqI := mkIdent `SEQ
      let seqT := mkIdent seqTypeName
      let entry ← `($ch $self $allDst $seqI $args*)
      return #[(← `(doElem| let $nxt:ident : $(ctx.nodeT) → $seqT :| ∀ $(mkIdent `net_dst):ident, $(seqOrd `next) ($sent $self $(mkIdent `net_dst)) ($nxt $(mkIdent `net_dst)))).raw,
        ← assign entry (← `(if $seqI = $sent $self $allDst then true else $entry)),
        ← assign (← `($sent $self $allDst)) (← `($nxt $allDst))] ++ count
  let ch := mkIdent (if ctx.cfg.synchrony == .sync then outChan k.name else netChan k.name)
  let entry ← `($ch $self $dst $args*)
  let update ← match ctx.cfg.synchrony == .async && ctx.cfg.multiset, guard? with
    | true, none => `(doElem| $entry:term := $entry + 1)
    | true, some g => `(doElem| $entry:term := $entry + if $g then 1 else 0)
    | false, none => `(doElem| $entry:term := true)
    | false, some g => `(doElem| $entry:term := decide ($entry = true ∨ $g))
  return #[update.raw] ++ count

/-- Whether the code always ends the step (with a `return`). -/
private partial def endsStep (code : Array Syntax) : Bool :=
  match code.back? with
  | none => false
  | some last =>
    if last.isOfKind ``Lean.Parser.Term.doReturn then true
    else if last.isOfKind ``Lean.Parser.Term.doIf && last[4].getNumArgs == 0 && last[5].getNumArgs == 2 then
      endsStep (doSeqElems last[3]) && endsStep (doSeqElems last[5][1])
    else false

mutual
/-- The code that runs `stmts`, then whatever `frames` say comes next.
`visited`: the loops whose head this step has already passed. -/
private partial def emit (stmts : List Stmt) (frames : List Frame) (visited : List Nat) (sc : Scope) :
    M (Array Syntax) := do
  match stmts with
  | [] =>
    match frames with
    | [] => suspendAt doneLabel true
    | .fallthrough :: _ => return #[]
    | .seq rest :: fs => emit rest fs visited sc.exit
    | .loopEnd id cond body :: fs => emitLoop id cond body fs visited sc.exit
  | s :: rest =>
    match s with
    | .plain e =>
      let bound ← boundBy e
      checkDead sc e bound
      let e' ← localize e
      let sc' := sc.bind bound
      return #[e'] ++ (← emit rest frames visited sc')
    | .send msg dst _ => return (← sendCode sc msg (some dst)) ++ (← emit rest frames visited sc)
    | .broadcast msg guard? _ => return (← sendCode sc msg none guard?) ++ (← emit rest frames visited sc)
    | .halt _ => suspendAt doneLabel true
    | .recv id _ _ ref =>
      if (← isSync) then
        throwErrorAt ref "`recv` is only available in asynchronous networks; in a synchronous network, end the round with `next_round` and inspect the messages with `received`"
      suspendAt (recvLabel id) false
    | .nextRound id ref =>
      unless (← isSync) do
        throwErrorAt ref "`next_round` is only available in synchronous networks"
      suspendAt (roundLabel id) true
    | .ite cond thn els _ =>
      checkDead sc cond
      let cond' ← localize cond
      let thnCode ← emit thn [.fallthrough] visited sc
      let elsCode ← emit els [.fallthrough] visited sc
      let ite ← mkIf cond' thnCode (if elsCode.isEmpty then none else some elsCode)
      if endsStep thnCode && endsStep elsCode then
        -- both branches end the step, so nothing after the `if` runs
        return #[ite]
      return #[ite] ++ (← emit rest frames visited sc)
    | .loop id cond body _ => emitLoop id cond body (.seq rest :: frames) visited sc

/-- Arrive at the head of loop `id`, with `frames` describing what follows
the loop. -/
private partial def emitLoop (id : Nat) (cond : Syntax) (body : List Stmt) (frames : List Frame)
    (visited : List Nat) (sc : Scope) : M (Array Syntax) := do
  if visited.contains id then
    modify fun ids => if ids.contains id then ids else ids.push id
    return ← suspendAt (loopLabel id) false
  checkDead sc cond
  let cond' ← localize cond
  -- every path through the body ends the step, so the code after the `if`
  -- only runs when the loop exits
  let bodyCode ← emit body [.loopEnd id cond body] (id :: visited) sc
  let afterCode ← emit [] frames visited sc
  return #[← mkIf cond' bodyCode none] ++ afterCode
end

/-! ### Assembling the module -/

private def arrows (doms : Array Term) (cod : Term) : CommandElabM Term :=
  doms.foldrM (fun d acc => `($d → $acc)) cod

private partial def splitArrows (t : Term) : Array Term × Term :=
  match t with
  | `($a → $b) => let (ds, c) := splitArrows b; (#[a] ++ ds, c)
  | _ => (#[], t)

private def isBool (t : Term) : Bool := t.raw.isIdent && t.raw.getId == `Bool

private def mkForall (binders : Array (Ident × Term)) (body : Term) : CommandElabM Term := do
  let bs ← binders.mapM fun (x, t) => `(bracketedBinder| ($x:ident : $t))
  `(∀ $bs*, $body)

private def capitals (n : Nat) : Array Ident :=
  (Array.range n).map fun i => mkIdent (Name.mkSimple s!"A{i + 1}")

private def mkAction (name : Name) (params : Array (Ident × Term)) (body : Array Syntax) :
    M (TSyntax `command) := do
  let body ← mkSeq body
  let name := mkIdent name
  if params.isEmpty then
    `(command| action $name:ident { $body:doSeq })
  else
    let bs ← params.mapM fun (x, t) => `(bracketedExplicitBinders| ($x:ident : $t))
    let bs ← `(explicitBinders| $bs*)
    `(command| action $name:ident $bs:explicitBinders { $body:doSeq })

/-- The channel entry `ch src dst args`, its "present" condition, and the
statement that removes it. -/
private def channelOps (ch : Ident) (src dst : Term) (args : Array Term) : M (Term × TSyntax `doElem) := do
  let entry ← `($ch $src $dst $args*)
  if (← read).cfg.multiset then
    return (← `($entry > 0), ← `(doElem| $entry:term := $entry - 1))
  else
    return (← `($entry = true), ← `(doElem| $entry:term := false))

private def resumeAction (r : Resume) (multiArm : Nat → Bool) : M (TSyntax `command) := do
  let ctx ← read
  let self := ctx.self
  match r with
  | .recvArm id i pat body frames dead =>
    let k := pat.kind
    let args : Array Term := pat.args.map (fun (x, _) => (x : Term))
    let mut code ← requireAt (recvLabel id)
    for (x, sel) in pat.args do
      if let some t := sel then
        let t ← userTerm { dead } t
        code := code.push (← `(doElem| require $x = $t))
    let ch := mkIdent (netChan k.name)
    let mut params := #[(self, ctx.nodeT), (pat.src, ctx.nodeT)] ++
      (pat.args.zip k.fields).map fun ((x, _), (_, t)) => (x, t)
    if ctx.cfg.fifo then
      let recvd ← `($(mkIdent seqRecvName) $(pat.src) $self)
      let nxt := mkIdent `net_seq_next
      if ctx.cfg.lossy then
        -- receive any later message: the ones skipped over are lost
        let seqI := mkIdent (freshName (pat.binders.insert self.getId) `seq)
        params := params.push (seqI, mkIdent seqTypeName)
        code := code.push (← `(doElem| require $ch $(pat.src) $self $seqI $args* = true))
        code := code.push (← `(doElem| require $(seqOrd `le) $recvd $seqI))
        let seqCap := mkIdent `SEQ
        for k' in ctx.messages do
          let ch' := mkIdent (netChan k'.name)
          let entry ← `($ch' $(pat.src) $self $seqCap $(capitals k'.fields.size)*)
          -- written as `if`: Veil's SMT encoding does not support `&& decide _` here
          code := code.push (← assign entry (← `(if $(seqOrd `lt) $seqCap $seqI then false else $entry)))
        code := code.push (← assign (← `($ch $(pat.src) $self $seqI $args*)) (← `(false)))
        code := code.push (← `(doElem| let $nxt:ident :| $(seqOrd `next) $seqI $nxt))
      else
        -- only the next message in the channel can be received
        code := code.push (← `(doElem| require $ch $(pat.src) $self $recvd $args* = true))
        code := code.push (← assign (← `($ch $(pat.src) $self $recvd $args*)) (← `(false)))
        code := code.push (← `(doElem| let $nxt:ident :| $(seqOrd `next) $recvd $nxt))
      code := code.push (← assign recvd nxt)
    else
      let (present, consume) ← channelOps ch pat.src self args
      code := code.push (← `(doElem| require $present))
      code := code.push consume
    let sc : Scope := { dead := pat.binders.foldl (·.erase ·) dead, bound := pat.binders }
    code := code ++ (← emit body frames [] sc)
    let suffix := if multiArm id then s!"_{i + 1}" else ""
    mkAction (Name.mkSimple s!"node_recv{id}_{k.name}{suffix}") params code
  | .loopHead id cond body frames dead =>
    let code := (← requireAt (loopLabel id)) ++ (← emitLoop id cond body frames [] { dead })
    mkAction (Name.mkSimple s!"node_loop{id}") #[(self, ctx.nodeT)] code
  | .round id body frames dead =>
    let code := (← requireAt (roundLabel id)) ++ (← emit body frames [] { dead })
    mkAction (Name.mkSimple s!"node_round{id}") #[(self, ctx.nodeT)] code


@[command_elab programDeclaration]
def elabProgram : CommandElab := fun stx => do
  let (mod, decls) ← openDecls "program"
  if (← getCurrentModule)._stateDefined then
    throwError "the state of this module is already fixed, but `program` generates it: put `program` \
      before `#gen_state`, ghost definitions, `assumption`s and properties"
  let some cfg := decls.config | unreachable!
  let self : Ident := ⟨stx[2]⟩
  let nodeT : Term := ⟨stx[4]⟩
  let body := stx[7]
  let sync := cfg.synchrony == .sync
  let msgs := decls.messages
  let varNames : NameSet := decls.vars.foldl (·.insert ·.name) {}

  -- the state the compiler generates
  let mut generated : Array Name := #[pcName, pcType, emptyName, haltedName]
  for k in msgs do
    generated := generated ++ (if sync then #[outChan k.name, inChan k.name] else #[netChan k.name])
  if sync then generated := generated.push readyName
  if cfg.complexity then
    generated := generated ++ #[msgsName, bcastsName] ++ (if sync then #[roundsName] else #[])
  generated := generated.push correctName
  if cfg.crash then
    generated := generated ++ #[crashedName, crashesName] ++ (if sync then #[crashingName] else #[])
  if cfg.faults matches .byzantine none then generated := generated.push byzName
  if cfg.fifo then generated := generated ++ #[seqTypeName, seqOrderName, seqSentName, seqRecvName]
  for v in decls.vars do
    if generated.contains v.name then
      throwErrorAt v.ref "`{v.name}` is the name of a component the compiler generates; choose another name"
  let mut forbidden : NameMap MessageData := {}
  for n in generated do
    forbidden := forbidden.insert n m!"a node program cannot access `{n}`: it is part of the network \
      and scheduler state that `program` generates"
  if let some p := byzPred cfg then
    for n in identsIn p do
      forbidden := forbidden.insert n m!"a node program cannot access `{n}`: it tells which nodes \
        are Byzantine, which nodes do not know"
  for sc in (← getCurrentModule).signature do
    if sc.mutability == .mutable && !varNames.contains sc.name then
      forbidden := forbidden.insert sc.name m!"`{sc.name}` is shared state, which a node program \
        cannot access: a node can only use its own `var`s, and communicate with `send` and `recv`"
  let varArity : NameMap Nat := decls.vars.foldl (init := {}) fun m v =>
    m.insert v.name (splitArrows v.ty).1.size
  let ctx : Ctx := { cfg, self, nodeT, messages := msgs, varNames, varArity, forbidden }

  -- parse, and find the resume points
  let reserved := varNames.insert self.getId
  let (prog, _) ← (parseSeq body).run { msgs, reserved } |>.run 0
  let ((), resumes) ← (collect prog [] {}).run #[]

  let cmds ← (show M (Array (TSyntax `command)) from do
    -- The node's actions come first, since generating them tells which loop
    -- heads are ever suspended at.
    let mut entry ← requireAt startLabel
    if let some p := byzPred cfg then
      -- Byzantine nodes do not run the program
      entry := entry.push (← `(doElem| require ¬ $p $self))
    entry := entry ++ (← emit prog [] [] {})
    let mut actions := #[← mkAction `node_start #[(self, nodeT)] entry]
    -- an alternative's action is named after its message kind, and numbered
    -- only when several alternatives of one `recv` receive the same kind
    let multiArm (id : Nat) : Bool :=
      let ks := resumes.filterMap fun
        | .recvArm id' _ pat .. => if id' == id then some pat.kind.name else none
        | _ => none
      ks.any fun k => (ks.filter (· == k)).size > 1
    let mut labels := #[startLabel, doneLabel] ++ (if cfg.crash then #[crashedLabel] else #[])
    for r in resumes do
      match r with
      | .loopHead .. => pure ()
      | .recvArm id i .. =>
        if i == 0 then labels := labels.push (recvLabel id)
        actions := actions.push (← resumeAction r multiArm)
      | .round id .. =>
        labels := labels.push (roundLabel id)
        actions := actions.push (← resumeAction r multiArm)
    -- a loop head's action can itself suspend at other loop heads
    let mut loopsDone : Array Nat := #[]
    repeat
      let some id := (← get).find? (!loopsDone.contains ·) | break
      loopsDone := loopsDone.push id
      for r in resumes do
        if let .loopHead id' .. := r then
          if id' == id then
            labels := labels.push (loopLabel id)
            actions := actions.push (← resumeAction r multiArm)

    let mut cmds : Array (TSyntax `command) := #[]
    let pc := mkIdent pcName
    let seqT := mkIdent seqTypeName
    let byz? := byzPred cfg
    -- the domain of a channel: sender, receiver, sequence number (for `fifo`), fields
    let chanDom (k : MessageKind) : Array Term :=
      #[nodeT, nodeT] ++ (if cfg.fifo then #[(seqT : Term)] else #[]) ++ k.fields.map (·.2)
    -- capitalised indices covering a whole channel, after sender and receiver
    let chanCaps (k : MessageKind) : Array Ident :=
      (if cfg.fifo then #[mkIdent `SEQ] else #[]) ++ capitals k.fields.size
    let chans (k : MessageKind) : Array Name :=
      if sync then #[outChan k.name, inChan k.name] else #[netChan k.name]
    let counted := !sync && cfg.multiset
    if cfg.fifo then
      cmds := cmds.push (← `(command| type $seqT:ident))
      cmds := cmds.push (← `(command| instantiate $(mkIdent seqOrderName):ident : $(mkIdent `TotalOrderWithMinimum) $seqT))
    if cfg.faults matches .byzantine none then
      cmds := cmds.push (← `(command| immutable relation $(mkIdent byzName):ident : $nodeT → Bool))
    -- program counter
    cmds := cmds.push (← `(command| enum $(mkIdent pcType):ident = { $labels,* }))
    cmds := cmds.push (← `(command| function $pc:ident : $nodeT → $(mkIdent pcType)))
    -- node variables
    for v in decls.vars do
      let (doms, cod) := splitArrows v.ty
      let ty ← arrows (#[nodeT] ++ doms) cod
      let x := mkIdentFrom v.ref v.name
      cmds := cmds.push (← if isBool cod then `(command| relation $x:ident : $ty) else `(command| function $x:ident : $ty))
    -- channels
    for k in msgs do
      for ch in chans k do
        let ch := mkIdent ch
        if counted then
          cmds := cmds.push (← `(command| function $ch:ident : $(← arrows (chanDom k) (← `(Nat)))))
        else
          cmds := cmds.push (← `(command| relation $ch:ident : $(← arrows (chanDom k) (← `(Bool)))))
    if cfg.fifo then
      for c in #[seqSentName, seqRecvName] do
        cmds := cmds.push (← `(command| function $(mkIdent c):ident : $nodeT → $nodeT → $seqT))
    if sync then
      cmds := cmds.push (← `(command| relation $(mkIdent readyName):ident : $nodeT → Bool))
    if cfg.crash then
      cmds := cmds.push (← `(command| individual $(mkIdent crashesName):ident : Nat))
      if sync then
        cmds := cmds.push (← `(command| relation $(mkIdent crashingName):ident : $nodeT → Bool))
    if cfg.complexity then
      for c in #[msgsName, bcastsName] ++ (if sync then #[roundsName] else #[]) do
        cmds := cmds.push (← `(command| individual $(mkIdent c):ident : Nat))
    cmds := cmds.push (← `(command| #gen_state))

    -- ghost relations for specifications
    let n := mkIdent `n
    cmds := cmds.push (← `(command| ghost relation $(mkIdent haltedName):ident ($n:ident : $nodeT) := $pc $n = $doneLabel))
    let correctDef ← match cfg.faults with
      | .none => `(True)
      | .crash _ => `($pc $n ≠ $crashedLabel)
      | .byzantine _ => `(¬ $(byz?.get!) $n)
    cmds := cmds.push (← `(command| ghost relation $(mkIdent correctName):ident ($n:ident : $nodeT) := $correctDef))
    if cfg.crash then
      cmds := cmds.push (← `(command| ghost relation $(mkIdent crashedName):ident ($n:ident : $nodeT) := $pc $n = $crashedLabel))
    let mut empties : Array Term := #[]
    for k in msgs do
      let ch := mkIdent (if sync then outChan k.name else netChan k.name)
      let (src, dst) := (mkIdent `S, mkIdent `D)
      let xs := chanCaps k
      let isEmpty ← if counted then `($ch $src $dst $xs* = 0) else `($ch $src $dst $xs* = false)
      empties := empties.push (← mkForall (#[src, dst] ++ xs |>.zip (chanDom k)) isEmpty)
    let emptyDef ← if empties.isEmpty then `(True) else empties[1:].foldlM (fun acc e => `($acc ∧ $e)) empties[0]!
    cmds := cmds.push (← `(command| ghost relation $(mkIdent emptyName):ident := $emptyDef))

    -- initial state
    let (allN, allS, allD) := (mkIdent `N, mkIdent `S, mkIdent `D)
    let mut init : Array Syntax := #[]
    init := init.push (← assign (← `($pc $allN)) startLabel)
    for v in decls.vars do
      let x := mkIdentFrom v.ref v.name
      match v.init with
      | none => pure ()
      | some none =>
        let lhs : Term := x
        init := init.push (← `(doElem| $lhs:term := *))
      | some (some e) =>
        let xs := capitals (splitArrows v.ty).1.size
        let nself := mkIdent `NSELF
        let mentionsSelf := (identsIn e).contains `self
        let val ← if mentionsSelf then `((let $(mkIdent `self) := $nself; $e))
          else if xs.isEmpty then pure e else `(($e))
        let val ← if xs.isEmpty then pure val else `($val $xs*)
        init := init.push (← assign (← `($x $nself $xs*)) val)
    for k in msgs do
      for ch in chans k do
        init := init.push (← assign (← `($(mkIdent ch) $allS $allD $(chanCaps k)*))
          (← if counted then `(0) else `(false)))
    if cfg.fifo then
      for c in #[seqSentName, seqRecvName] do
        init := init.push (← assign (← `($(mkIdent c) $allS $allD)) (seqOrd `zero))
    if sync then
      init := init.push (← assign (← `($(mkIdent readyName) $allN)) (← `(decide $(← running cfg allN))))
    if cfg.crash then
      init := init.push (← `(doElem| $(mkIdent crashesName):ident := 0))
      if sync then
        init := init.push (← assign (← `($(mkIdent crashingName) $allN)) (← `(false)))
    if cfg.complexity then
      for c in #[msgsName, bcastsName] ++ (if sync then #[roundsName] else #[]) do
        init := init.push (← `(doElem| $(mkIdent c):ident := 0))
    cmds := cmds.push (← `(command| after_init { $(← mkSeq init):doSeq }))

    -- the node's actions
    cmds := cmds ++ actions

    -- the network's actions, on a message of each kind
    for k in msgs do
      let fieldNames : NameSet := k.fields.foldl (·.insert ·.1.getId) {}
      let src := mkIdent (freshName fieldNames `src)
      let dst := mkIdent (freshName fieldNames `dst)
      let seqI := mkIdent (freshName fieldNames `seq)
      let xs : Array Term := k.fields.map (·.1)
      let params := #[(src, nodeT), (dst, nodeT)] ++ (if cfg.fifo then #[(seqI, (seqT : Term))] else #[]) ++ k.fields
      let ch := mkIdent (if sync then outChan k.name else netChan k.name)
      let msgEntry ← if cfg.fifo then `($ch $src $dst $seqI $xs*) else `($ch $src $dst $xs*)
      -- lose a message: in flight (`async`), or sent in the current round (`sync`),
      -- where a node that crashes in a round may also lose some of its messages
      if cfg.lossy || (sync && cfg.crash) then
        let mut code : Array Syntax := #[]
        if counted then
          code := code.push (← `(doElem| require $msgEntry > 0))
          code := code.push (← assign msgEntry (← `($msgEntry - 1)))
        else
          code := code.push (← `(doElem| require $msgEntry = true))
          if !cfg.lossy then
            code := code.push (← `(doElem| require $(mkIdent crashingName) $src = true))
          code := code.push (← assign msgEntry (← `(false)))
        cmds := cmds.push (← mkAction (k.name.appendBefore "net_drop_") params code)
      -- a Byzantine node sends anything
      if let some p := byz? then
        let update ← if counted then `($msgEntry + 1) else `(true)
        cmds := cmds.push (← mkAction (k.name.appendBefore "net_byz_send_") params
          #[(← `(doElem| require $p $src)).raw, ← assign msgEntry update])
    if cfg.crash then
      let mut code : Array Syntax := #[]
      code := code.push (← `(doElem| require $pc $n ≠ $doneLabel ∧ $pc $n ≠ $crashedLabel))
      if let .crash (some bound) := cfg.faults then
        code := code.push (← `(doElem| require $(mkIdent crashesName) < $bound))
      code := code.push (← assign (← `($pc $n)) crashedLabel)
      let c := mkIdent crashesName
      code := code.push (← `(doElem| $c:ident := $c + 1))
      if sync then
        code := code.push (← assign (← `($(mkIdent readyName) $n)) (← `(false)))
        code := code.push (← assign (← `($(mkIdent crashingName) $n)) (← `(true)))
      cmds := cmds.push (← mkAction `net_crash #[(n, nodeT)] code)
    if sync then
      let mut code : Array Syntax := #[]
      code := code.push (← `(doElem| require ∀ $n:ident, $(mkIdent readyName):ident $n = false))
      code := code.push (← `(doElem| require ∃ $n:ident, $(← running cfg n)))
      for k in msgs do
        let out := mkIdent (outChan k.name)
        let inb := mkIdent (inChan k.name)
        let xs := chanCaps k
        code := code.push (← assign (← `($inb $allS $allD $xs*)) (← `($out $allS $allD $xs*)))
        code := code.push (← assign (← `($out $allS $allD $xs*)) (← `(false)))
      if cfg.crash then
        code := code.push (← assign (← `($(mkIdent crashingName) $allN)) (← `(false)))
      code := code.push (← assign (← `($(mkIdent readyName) $allN)) (← `(decide $(← running cfg allN))))
      if cfg.complexity then
        let r := mkIdent roundsName
        code := code.push (← `(doElem| $r:ident := $r + 1))
      cmds := cmds.push (← mkAction `net_next_round #[] code)
    return cmds).run ctx |>.run' #[]

  modifyDecls mod ({ · with programDone := true, program? := some (stx, cmds) })
  withRef stx do
    for cmd in cmds do
      elabVeilCommand cmd

/-! ## `#desugar_program` -/

/-- Make generated syntax printable as source: drop source positions, and the
macro scopes hygiene adds to identifiers (they print as `x✝`). Generated
binders use reserved names (`net_src`, ...), so this captures nothing. -/
private partial def toPrintable : Syntax → Syntax
  | .ident _ raw val pre => .ident .none raw val.eraseMacroScopes pre
  | .node _ kind args => .node .none kind (args.map toPrintable)
  | .atom _ val => .atom .none val
  | .missing => .missing

private def ppTerm' (t : Syntax) : CoreM String :=
  return (← PrettyPrinter.ppTerm ⟨t⟩).pretty 100

private def indentLines (indent : String) (text : String) : String :=
  "\n".intercalate (text.splitOn "\n" |>.map (indent ++ ·))

/-- Print a `do` block, one statement per line at `indent`. Lean's formatter
lays out a block with a stray space before pattern assignments (`f x := e`),
which breaks the alignment `do` blocks need; so blocks and `if`s are laid out
here, and the formatter only prints single statements. -/
private partial def printDoSeq (indent : String) (seq : Syntax) : CoreM String := do
  let mut lines : Array String := #[]
  for e in doSeqElems seq do
    if e.isOfKind ``Lean.Parser.Term.doIf && e[4].getNumArgs == 0 then
      let cond := e[1]
      let hyp := if cond[0].getNumArgs == 0 then "" else s!"{cond[0][0].getId} : "
      let mut out := s!"{indent}if {hyp}{← ppTerm' cond[1]} then\n{← printDoSeq (indent ++ "  ") e[3]}"
      if e[5].getNumArgs == 2 then
        out := out ++ s!"\n{indent}else\n{← printDoSeq (indent ++ "  ") e[5][1]}"
      lines := lines.push out
    else if let `(doElem| let $x:term $[: $ty:term]? :| $[$h:ident :]? $p) := e then
      -- `let x : T :| P` (the formatter prints it without spaces)
      let ty ← if let some ty := ty then pure s!" : {← ppTerm' ty}" else pure ""
      let hyp := if let some h := h then s!"{h.getId} : " else ""
      lines := lines.push s!"{indent}let {← ppTerm' x}{ty} :| {hyp}{← ppTerm' p}"
    else
      let text := ((← PrettyPrinter.ppCategory `doElem e).pretty 100).trimAsciiStart.toString
      lines := lines.push (indentLines indent text)
  return "\n".intercalate lines.toList

/-- The first token in `s`, e.g. the keyword of a keyword node. -/
private partial def firstAtom (s : Syntax) : String :=
  match s with
  | .atom _ v => v
  | .node _ _ args => args.foldl (fun acc a => if acc.isEmpty then firstAtom a else acc) ""
  | _ => ""

/-- Print one generated command as source text. -/
private def printCommand (cmd : Syntax) : CoreM String := do
  let k := cmd.getKind
  if k == ``Veil.stateComponentDeclaration then
    let mutability := if cmd[0].getNumArgs == 0 then "" else s!"{firstAtom cmd[0]} "
    return s!"{mutability}{firstAtom cmd[1]} {cmd[2].getId} : {← ppTerm' cmd[4][1]}"
  if k == ``Veil.enumDeclaration then
    let ctors := cmd[4].getSepArgs.map (·.getId.toString)
    return s!"enum {cmd[1].getId} = \{{", ".intercalate ctors.toList}}"
  if k == ``Veil.ghostRelationDefinition then
    let binders ← if cmd[4].getNumArgs == 0 then pure "" else
      pure (" " ++ ((← PrettyPrinter.ppCategory ``Lean.explicitBinders cmd[4][0]).pretty 100).trimAscii.toString)
    return s!"ghost relation {cmd[3].getId}{binders} :=\n  {← ppTerm' cmd[6]}"
  if k == ``Veil.initializerDefinition then
    return s!"after_init \{\n{← printDoSeq "  " cmd[2]}\n}"
  if k == ``Veil.procedureDefinition then
    let binders ← if cmd[2].getNumArgs == 0 then pure "" else
      pure (" " ++ ((← PrettyPrinter.ppCategory ``Lean.explicitBinders cmd[2][0]).pretty 100).trimAscii.toString)
    return s!"{firstAtom cmd[0]} {cmd[1].getId}{binders} \{\n{← printDoSeq "  " cmd[4]}\n}"
  return (← PrettyPrinter.ppCommand ⟨cmd⟩).pretty 100

/-- Whether `s` is only whitespace, comments, and a `#guard_msgs … in` prefix:
what may separate `#desugar_program` from its `program`. -/
private partial def onlyTrivia (s : String) : Bool :=
  let s := s.trimAscii.toString
  if s.isEmpty then true
  else if s.startsWith "/-" then
    match s.splitOn "-/" with
    | _ :: rest@(_ :: _) => onlyTrivia ("-/".intercalate rest)
    | _ => false
  else if s.startsWith "--" then
    match s.splitOn "\n" with
    | _ :: rest => onlyTrivia ("\n".intercalate rest)
    | [] => true
  else if s.startsWith "#guard_msgs" then
    match s.splitOn " in" with
    | _ :: rest@(_ :: _) => onlyTrivia (" in".intercalate rest)
    | _ => false
  else false

@[command_elab desugarProgramCmd]
def elabDesugarProgram : CommandElab := fun stx => do
  let mod ← currentModuleName "#desugar_program"
  let some (progStx, cmds) := (← getDecls mod).program?
    | throwError "`#desugar_program` must come after a `program`"
  -- the suggestion replaces the `program` and this command, so nothing may
  -- lie between them
  let source := (← getFileMap).source
  if let (some progEnd, some here) := (progStx.getTailPos?, stx.getPos?) then
    unless onlyTrivia (String.Pos.Raw.extract source progEnd here) do
      throwError "put `#desugar_program` directly after the `program` it desugars"
  let mut text := ""
  for cmd in cmds do
    text := text ++ (if text.isEmpty then "" else "\n\n") ++ (← liftCoreM <| printCommand (toPrintable cmd))
  let suggestion : Lean.Meta.Tactic.TryThis.Suggestion := {
    suggestion := .string text
    toCodeActionTitle? := some fun _ => "Replace `program` with the plain Veil it compiles to"
  }
  liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion (mkNullNode #[progStx, stx]) suggestion
    (header := "The plain Veil this `program` compiles to:\n")

end Veil.Distributed
