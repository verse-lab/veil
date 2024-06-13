import Mathlib.Tactic
import LeanSts.BFT.Byzantine

structure NetworkPacket {NetAddr Message : Type} :=
  src : NetAddr
  dst : NetAddr
  msg : Message
  consumed: Bool
deriving DecidableEq

abbrev Packet (NetAddr Message : Type) := @NetworkPacket NetAddr Message

namespace Packet
private def receive (p : Packet NetAddr Message) : Packet NetAddr Message :=
  { p with consumed := true }

def consume [DecidableEq (Packet NetAddr Message)] (p : Packet NetAddr Message) (soup : Multiset (Packet NetAddr Message)) : Multiset (Packet NetAddr Message) :=
  (soup.erase p) + {receive p}

def broadcast [DecidableEq NetAddr] (src : NetAddr) (dsts : List NetAddr) (msg : Message) : List (Packet NetAddr Message) :=
  dsts.map (λ dst => { src := src, dst := dst, msg := msg, consumed := false })
end Packet

class NetworkProtocol {NetAddr Message LocalState InternalTransition : Type} :=
  localInit : NetAddr → LocalState
  procInternal : LocalState → InternalTransition → LocalState × List (Packet NetAddr Message)
  procMessage : LocalState → NetAddr /- sender -/ → Message → LocalState × List (Packet NetAddr Message)

/-- A network consists of the packet soup and the local states of nodes.
  Informally, this is called a "World". -/
structure NetworkState {NetAddr Packet LocalState : Type} :=
  /-- The set of all nodes in the network. -/
  nodes: List NetAddr
  /-- The respective local state of nodes. -/
  localState : NetAddr → LocalState
  /-- The set of sent messages. -/
  packetSoup : Multiset Packet

@[simp] def updNS {NetAddr LocalState : Type} [DecidableEq NetAddr]
  (n : NetAddr) (st : LocalState) (states : NetAddr → LocalState) : NetAddr → LocalState :=
  λ n' => if n = n' then st else states n'

namespace AsynchronousNetwork
  abbrev World {NetAddr Packet LocalState : Type} := @NetworkState NetAddr Packet LocalState

  def init [protocol : @NetworkProtocol NetAddr Message LocalState InternalTransition]
    (nodes : List NetAddr) : (@NetworkState NetAddr (Packet NetAddr Message) LocalState) :=
    { nodes := nodes, localState := protocol.localInit, packetSoup := ∅ }

  /-- Description of a step being taken. -/
  inductive step {NetAddr Message Packet InternalTransition : Type}
    /-- Stuttering. -/
    | idle
    /-- Packet `p` is delivered to its recipient. -/
    | deliver (p : Packet)
    /-- Node `proc` executes `transition`. -/
    | intern (proc : NetAddr) (transition : InternalTransition)
    /-- The Byzantine adversary creates a packet. -/
    | byz (p : Packet)

  /-- Transition relation of this network. -/
  inductive transition
    [DecidableEq NetAddr] [DecidableEq Message]
    [protocol : @NetworkProtocol NetAddr Message LocalState InternalTransition]
    [byz : @NonadaptiveByzantineAdversary NetAddr (Packet NetAddr Message) (@NetworkState NetAddr (Packet NetAddr Message) LocalState)]
    (s : @step NetAddr Message (Packet NetAddr Message) InternalTransition)
    (w w' : @World NetAddr (Packet NetAddr Message) LocalState)
    /-- Stuttering. -/
    | idle (_ : s = step.idle) (_ : w = w')

    /-- Packet `p` is delivered to its recipient. -/
    | deliver (p : (Packet NetAddr Message))
      (_ : s = step.deliver p)
      (_ : p ∈ w.packetSoup)
      (_ : ¬ byz.isByzantine p.dst)
      (_ : let (st', msgs) := protocol.procMessage (w.localState p.dst) p.src p.msg
          w' = { w with localState := updNS p.dst st' w.localState,
                        packetSoup := Packet.consume p w.packetSoup + msgs })

    /-- Node `proc` executes internal transition `t`. -/
    | intern (proc : NetAddr) (t : InternalTransition)
      (_ : s = step.intern proc t)
      (_ : ¬ byz.isByzantine proc)
      (_ : let (st', msgs) := protocol.procInternal (w.localState proc) t
          w' = { w with localState := updNS proc st' w.localState,
                        packetSoup := w.packetSoup + msgs })

    /-- The Byzantine adversary creates a packet. -/
    | byzantine (p : (Packet NetAddr Message))
      (_ : s = step.byz p)
      /- In Coq, we have an extra assumption:
          `(_ : byz.setting.isByzantine src w)`
        but this should not be part of the semantics itself.
        Instead, we fold it into `canProducePacket`.
      -/
      (_ : byz.constraint.canProducePacket p w)
      (_ : w' = { w with packetSoup := w.packetSoup + {p}})

end AsynchronousNetwork
