import Mathlib.Tactic
import LeanSts.BFT.Byzantine

structure NetworkPacket {NetAddr Message : Type} :=
  src : NetAddr
  dst : NetAddr
  msg : Message
  consumed: Bool
deriving DecidableEq

abbrev Packet (NetAddr Message : Type) := @NetworkPacket NetAddr Message

def receive (p : Packet NetAddr Message) : Packet NetAddr Message :=
  { p with consumed := true }

class NetworkProtocol {NetAddr Message LocalState InternalTransition : Type} :=
  localInit : NetAddr → LocalState
  procInternal : LocalState → InternalTransition → LocalState × List (Packet NetAddr Message)
  procMessage : LocalState → NetAddr /- sender -/ → Message → LocalState × List (Packet NetAddr Message)

/-- A network consists of the packet soup and the local states of nodes.
  Informally, this is called a "World". -/
structure NetworkState {NetAddr Packet LocalState : Type} :=
  /-- The respective local state of nodes. -/
  localState : NetAddr → LocalState
  /-- The set of sent messages. -/
  packetSoup : Multiset Packet

def consume [DecidableEq (Packet NetAddr Message)] (p : Packet NetAddr Message) (soup : Multiset (Packet NetAddr Message)) : Multiset (Packet NetAddr Message) :=
  (soup.erase p) + {receive p}

@[simp] def updNS {NetAddr LocalState : Type} [DecidableEq NetAddr]
  (n : NetAddr) (st : LocalState) (states : NetAddr → LocalState) : NetAddr → LocalState :=
  λ n' => if n = n' then st else states n'

theorem defaultNetworkState
  [protocol : @NetworkProtocol NetAddr Message LocalState InternalTransition]
  : Inhabited (@NetworkState NetAddr (Packet NetAddr Message) LocalState) :=
  ⟨{ localState := λ n => protocol.localInit n, packetSoup := ∅ }⟩

namespace AsynchronousNetwork
  abbrev World {NetAddr Packet LocalState : Type} := @NetworkState NetAddr Packet LocalState

  /-- Description of a step being taken. -/
  inductive step {NetAddr Message Packet InternalTransition : Type}
    /-- Stuttering. -/
    | idle
    /-- Packet `p` is delivered to its recipient. -/
    | deliver (p : Packet)
    /-- Node `proc` executes `transition`. -/
    | intern (proc : NetAddr) (transition : InternalTransition)
    /-- The Byzantine adversary creates a message. -/
    | byz (src dst : NetAddr) (msg : Message)

  /-- Transition relation of this network. -/
  inductive transition
    [DecidableEq NetAddr] [DecidableEq Message]
    [protocol : @NetworkProtocol NetAddr Message LocalState InternalTransition]
    [byz : @ByzantineAdversary NetAddr Message (@NetworkState NetAddr (Packet NetAddr Message) LocalState)]
    (s : @step NetAddr Message (Packet NetAddr Message) InternalTransition)
    (w w' : @World NetAddr (Packet NetAddr Message) LocalState)
    /-- Stuttering. -/
    | idle (_ : s = step.idle) (_ : w = w')

    /-- Packet `p` is delivered to its recipient. -/
    | deliver (p : (Packet NetAddr Message))
      (_ : s = step.deliver p)
      (_ : p ∈ w.packetSoup)
      (_ : ¬ byz.setting.isByzantine p.dst w)
      (_ : let (st', msgs) := protocol.procMessage (w.localState p.dst) p.src p.msg
          w' = { w with localState := updNS p.dst st' w.localState,
                        packetSoup := consume p w.packetSoup + msgs })

    /-- Node `proc` executes internal transition `t`. -/
    | intern (proc : NetAddr) (t : InternalTransition)
      (_ : s = step.intern proc t)
      (_ : ¬ byz.setting.isByzantine proc w)
      (_ : let (st', msgs) := protocol.procInternal (w.localState proc) t
          w' = { w with localState := updNS proc st' w.localState,
                        packetSoup := w.packetSoup + msgs })

    /-- The Byzantine adversary creates a message. -/
    | byzantine (src dst : NetAddr) (msg : Message)
      (_ : s = step.byz src dst msg)
      (_ : byz.setting.isByzantine src w)
      (_ : byz.constraint.canProduceMessage msg w)
      (_ : let pkt := { src := src, dst := dst, msg := msg, consumed := false }
        w' = { w with packetSoup := w.packetSoup + {pkt}})

end AsynchronousNetwork
