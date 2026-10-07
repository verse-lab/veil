module

public import Veil

veil module GermanCacheCoherence

enum CacheState = { cI, cS, cE }
enum MsgCmd = { empty, reqS, reqE, inv, invAck, gntS, gntE }

-- CACHE == [State: CACHE_STATE, Data: DATA]
@[veil_decl]
structure CacheEntry (CacheState d : Type) where
  state : CacheState
  dat   : d
deriving instance Veil.Enumeration for CacheEntry

-- MSG == [Cmd: MSG_CMD, Data: DATA]
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

veil_set_field_representation relation Veil.ArrayAsFinset
veil_set_field_representation function Veil.ArrayAsFinmap

#gen_state

-- TLA+:
-- Cache = [i ∈ NODE |-> [State |-> "I", Data |-> 1]]
-- Chan1..3 = [i ∈ NODE |-> [Cmd |-> "Empty", Data |-> 1]]
-- InvSet/ShrSet = [i ∈ NODE |-> FALSE]
-- ExGntd = FALSE, CurCmd = "Empty", CurPtr ∈ NODE
-- MemData = 1, AuxData = 1

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
-- TLA+: Chan1' = [Chan1 EXCEPT ![i].Cmd = "ReqS"]
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
  -- InvSet' = [j ∈ NODE |-> ShrSet[j]]
  invSet := shrSet
}

-- RecvReqE(i): Directory receives exclusive request from node i.
action RecvReqE (i : node) {
  require curCmd = empty
  require (chan1 i).cmd = reqE
  curCmd := reqE
  curPtr := i
  chan1 i := { chan1 i with cmd := empty }
  -- InvSet' = [j ∈ NODE |-> ShrSet[j]]
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
-- TLA+: Chan3' = [Chan3 EXCEPT ![i] = [Cmd |-> "InvAck",
--          Data |-> IF Cache[i].State = "E" THEN Cache[i].Data ELSE Chan3[i].Data]]
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
-- TLA+: IF ExGntd THEN ExGntd'=FALSE /\ MemData'=Chan3[i].Data ELSE UNCHANGED
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
-- TLA+: Chan2' = [Chan2 EXCEPT ![i] = [Cmd |-> "GntS", Data |-> MemData]]
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
-- TLA+: ∀ j ∈ NODE : ShrSet[j] = FALSE
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
-- TLA+: Cache' = [Cache EXCEPT ![i] = [State |-> "S", Data |-> Chan2[i].Data]]
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

#gen_spec

#model_check compiled
{ node := Fin 2, data := Fin 2 }
{ initData := 0 }

end GermanCacheCoherence
