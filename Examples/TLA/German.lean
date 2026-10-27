module

public import Veil

-- source: https://github.com/egolf-cs/scythe-fmcad2024/blob/acb63604327eaca12e0fae80195124411047f56f/run_tool/sketches/German.tla

veil module GermanCacheCoherence

enum CacheState = { cI, cS, cE }
enum MsgCmd = { empty, reqS, reqE, inv, invAck, gntS, gntE }

@[veil_decl]
structure CacheEntry (CacheState d : Type) where
  state : CacheState
  dat   : d
deriving instance Veil.Enumeration for CacheEntry

@[veil_decl]
structure MsgEntry (MsgCmd d : Type) where
  cmd : MsgCmd
  dat : d
deriving instance Veil.Enumeration for MsgEntry

-- Abstract types
type node
type data

-- Default/initial data value (TLA+ uses the constant 1)
immutable individual initData : data

-- Cache per node: [State, Data]
function cache : node → CacheEntry CacheState data

-- Chan1 per node: request channel (ReqS, ReqE)
function chan1 : node → MsgEntry MsgCmd data

-- Chan2 per node: grant/invalidation channel (GntS, GntE, Inv)
function chan2 : node → MsgEntry MsgCmd data

-- Chan3 per node: invalidation ack channel (InvAck)
function chan3 : node → MsgEntry MsgCmd data

-- Directory state
relation invSet : node → Bool     -- nodes to be invalidated
relation shrSet : node → Bool     -- nodes having S or E copies
individual exGntd : Bool          -- exclusive copy has been granted
individual curCmd : MsgCmd        -- current request being processed
individual curPtr : node          -- node that issued current request
individual memData : data         -- memory data
individual auxData : data         -- auxiliary: tracks latest written value

set_option veil.deferVCGeneration true

veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

after_init {
  cache I := ⟨cI, initData⟩
  chan1 I := ⟨empty, initData⟩
  chan2 I := ⟨empty, initData⟩
  chan3 I := ⟨empty, initData⟩
  invSet I := false
  shrSet I := false
  exGntd := false
  curCmd := empty
  curPtr := *              -- nondeterministic (TLA+: CurPtr ∈ NODE)
  memData := initData
  auxData := initData
}

-- SendReqS(i): Node i requests shared access.
action SendReqS (i : node) {
  require (chan1 i).cmd = empty
  require (cache i).state = cI
  chan1 i := { chan1 i with cmd := reqS }
}

-- SendReqE(i): Node i requests exclusive access.
action SendReqE (i : node) {
  require (chan1 i).cmd = empty
  require (cache i).state = cI ∨ (cache i).state = cS
  chan1 i := { chan1 i with cmd := reqE }
}

-- RecvReqS(i): Directory receives shared request from node i.
action RecvReqS (i : node) {
  require curCmd = empty
  require (chan1 i).cmd = reqS
  curCmd := reqS
  curPtr := i
  chan1 i := { chan1 i with cmd := empty }
  invSet := shrSet
}

-- RecvReqE(i): Directory receives exclusive request from node i.
action RecvReqE (i : node) {
  require curCmd = empty
  require (chan1 i).cmd = reqE
  curCmd := reqE
  curPtr := i
  chan1 i := { chan1 i with cmd := empty }
  invSet := shrSet
}

-- SendInv(i): Directory sends invalidation to node i.
action SendInv (i : node) {
  require (chan2 i).cmd = empty
  require invSet i
  require curCmd = reqE ∨ (curCmd = reqS ∧ exGntd = true)
  chan2 i := { chan2 i with cmd := inv }
  invSet i := false
}

-- SendInvAck(i): Node i acknowledges invalidation.
action SendInvAck (i : node) {
  require (chan2 i).cmd = inv
  require (chan3 i).cmd = empty
  chan2 i := { chan2 i with cmd := empty }
  chan3 i := ⟨invAck,
    if (cache i).state = cE then (cache i).dat else (chan3 i).dat⟩
  -- Invalidate the cache
  cache i := { cache i with state := cI }
}

-- RecvInvAck(i): Directory receives invalidation ack from node i.
action RecvInvAck (i : node) {
  require (chan3 i).cmd = invAck
  require curCmd ≠ empty
  chan3 i := { chan3 i with cmd := empty }
  shrSet i := false
  if exGntd then
    exGntd := false
    memData := (chan3 i).dat
}

-- SendGntS(i): Directory grants shared access to requesting node i.
action SendGntS (i : node) {
  require curCmd = reqS
  require curPtr = i
  require (chan2 i).cmd = empty
  require exGntd = false
  chan2 i := ⟨gntS, memData⟩
  shrSet i := true
  curCmd := empty
}

-- SendGntE(i): Directory grants exclusive access to requesting node i.
action SendGntE (i : node) {
  require curCmd = reqE
  require curPtr = i
  require (chan2 i).cmd = empty
  require exGntd = false
  require ∀ j, shrSet j = false
  chan2 i := ⟨gntE, memData⟩
  shrSet i := true
  exGntd := true
  curCmd := empty
}

-- RecvGntS(i): Node i receives shared grant.
action RecvGntS (i : node) {
  require (chan2 i).cmd = gntS
  cache i := ⟨cS, (chan2 i).dat⟩
  chan2 i := { chan2 i with cmd := empty }
}

-- RecvGntE(i): Node i receives exclusive grant.
action RecvGntE (i : node) {
  require (chan2 i).cmd = gntE
  cache i := ⟨cE, (chan2 i).dat⟩
  chan2 i := { chan2 i with cmd := empty }
}

-- Store(i, d): Node i writes data d (requires exclusive access).
action Store (i : node) (d : data) {
  require (cache i).state = cE
  cache i := { cache i with dat := d }
  auxData := d
}

invariant [ctrlProp]
  I ≠ J →
    ((cache I).state = cE → (cache J).state = cI) ∧
    ((cache I).state = cS → ((cache J).state = cI ∨ (cache J).state = cS))

invariant [DataProp]
  (exGntd = false → memData = auxData) ∧
  (∀ i : node, (cache i).state ≠ cI → (cache i).dat = auxData)

termination false

#gen_spec
#gen_executable

-- The check below uses the instance of the TLC model `Benchmarks/TLA/German.cfg`.
-- It is commented out; uncomment it to run it.
--
-- The instantiation (first `{ ... }` argument) sets the module's `type`s and `param`s:
-- * `node := Fin 3`: the nodes are `0`, `1`, `2` (cfg: `NODE = {n1,n2,n3}`).
-- * `data := Fin 3`: the data values are `0`, `1`, `2`, for TLA+'s `1`, `2`, `3`
--   (cfg: `DATA = {1,2,3}`).
-- The theory (second `{ ... }` argument) sets the module's `immutable` fields:
-- * `initData := 0`: the initial data value, TLA+'s `1`. The cfg has no counterpart, since the
--   TLA+ `Init` writes the constant `1`.
--
-- The other settings of the cfg:
-- * `INVARIANTS CtrlProp DataProp`: `#model_check` checks every `invariant` of the module, here
--   `ctrlProp` and `DataProp`.
-- * The cfg has no `CHECK_DEADLOCK`, so TLC checks for deadlocks. With `termination false`
--   above, Veil also reports every state without successors as a deadlock.
-- Options:
-- * `compiled` runs the search only in a compiled checker, not in Lean's interpreter.
-- * `(seenSet := HAMTMapShard)`: the sharded map of visited states uses `HAMTMapShard`.
/- EVAL
#model_check compiled
{ node := Fin 3, data := Fin 3 }
{ initData := 0 } (seenSet := HAMTMapShard)
-/

end GermanCacheCoherence
