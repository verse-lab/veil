import Mathlib.Tactic
import LeanSts.BFT.Byzantine

/-- Packets over the network. -/
structure NetworkPacket {NetAddr Message : Type} :=
  src : NetAddr
  dst : NetAddr
  msg : Message
  consumed: Bool
deriving DecidableEq

/-- Events within a single node, either internal within a protocol, or
  cross-protocol (input / output). We can think of these as "messages"
  along a channel (in the Go sense). -/
structure ChannelEvent {NetAddr Event : Type} :=
  proc : NetAddr
  tr : Event

-- TODO: add channel tags to support multiple channels?

abbrev Event (NetAddr Event : Type) := @ChannelEvent NetAddr Event
abbrev Packet (NetAddr Message : Type) := @NetworkPacket NetAddr Message

namespace Packet
private def receive (p : Packet NetAddr Message) : Packet NetAddr Message :=
  { p with consumed := true }

def consume [DecidableEq (Packet NetAddr Message)] (p : Packet NetAddr Message) (soup : Multiset (Packet NetAddr Message)) : Multiset (Packet NetAddr Message) :=
  (soup.erase p) + {receive p}

def broadcast [DecidableEq NetAddr] (src : NetAddr) (dsts : List NetAddr) (msg : Message) : List (Packet NetAddr Message) :=
  dsts.map (λ dst => { src := src, dst := dst, msg := msg, consumed := false })
end Packet

abbrev Network {NetAddr : Type} := List NetAddr

class NetworkProtocol {NetAddr LocalState InputEvent InternalEvent OutputEvent Message : Type} :=
  localInit : NetAddr → LocalState
  procInput : @Network NetAddr → LocalState → InputEvent → LocalState × List (Packet NetAddr Message) × List InternalEvent × List OutputEvent
  procInternal : @Network NetAddr → LocalState → InternalEvent → LocalState × List (Packet NetAddr Message) × List InternalEvent × List OutputEvent
  procMessage : @Network NetAddr → LocalState → NetAddr /- sender -/ → Message → LocalState × List (Packet NetAddr Message) × List InternalEvent × List OutputEvent

/-- A network consists of the packet soup and the local states of nodes.
  Informally, this is called a "World". -/
structure NetworkState {NetAddr LocalState InputEvent InternalEvent OutputEvent Packet : Type} :=
  /-- The set of all nodes in the network. -/
  nodes: @Network NetAddr
  /-- The respective local state of nodes. -/
  localState : NetAddr → LocalState

  /-- Channel-like cross-protocol communication within nodes. Input events. -/
  inputEvents : NetAddr → Multiset InputEvent
  /-- Events which nodes schedule for themselves to run later. -/
  internalEvents: NetAddr → Multiset InternalEvent
  /-- Channel-like cross-protocol communication within nodes. Output events. -/
  outputEvents : NetAddr → Multiset OutputEvent

  /-- The set of sent messages. -/
  packetSoup : Multiset Packet

@[simp] def updNS {NetAddr LocalState : Type} [DecidableEq NetAddr]
  (n : NetAddr) (st : LocalState) (states : NetAddr → LocalState) : NetAddr → LocalState :=
  λ n' => if n = n' then st else states n'

namespace AsynchronousNetwork
  abbrev World {NetAddr LocalState InputEvent InternalEvent OutputEvent Packet : Type} := @NetworkState NetAddr LocalState InputEvent InternalEvent OutputEvent Packet

  def init [protocol : @NetworkProtocol NetAddr LocalState InputEvent InternalEvent OutputEvent Message] (nodes : @Network NetAddr) :
  (@NetworkState NetAddr LocalState InputEvent InternalEvent OutputEvent (Packet NetAddr Message)) := {
      nodes := nodes
      localState := protocol.localInit
      inputEvents := fun _ => ∅
      internalEvents := fun _ => ∅
      outputEvents := fun _ => ∅
      packetSoup := ∅
    }

  /-- Description of a step being taken. -/
  inductive step {NetAddr InputEvent InternalEvent Message Packet : Type}
    /-- Stuttering. -/
    | idle
    /-- Packet `p` is delivered to its recipient. -/
    | deliver (p : Packet)
    /-- Node `proc` executes `transition`. -/
    | intern (proc : NetAddr) (transition : InternalEvent)
    /-- The Byzantine adversary creates a packet. -/
    | byz (p : Packet)

  /-- Transition relation of this network. -/
  inductive transition
    [DecidableEq NetAddr] [DecidableEq Message]
    [protocol : @NetworkProtocol NetAddr LocalState InputEvent InternalEvent OutputEvent Message]
    [byz : @NonadaptiveByzantineAdversary NetAddr (Packet NetAddr Message)
      (@NetworkState NetAddr LocalState InputEvent InternalEvent OutputEvent (Packet NetAddr Message))]
    (s : @step NetAddr InputEvent InternalEvent Message (Packet NetAddr Message))
    (w w' : @World NetAddr LocalState InputEvent InternalEvent OutputEvent (Packet NetAddr Message))
    /-- Stuttering. -/
    | idle (_ : s = step.idle) (_ : w = w')

    /-- Packet `p` is delivered to its recipient. -/
    | deliver (p : (Packet NetAddr Message))
      (_ : s = step.deliver p)
      (_ : p ∈ w.packetSoup)
      (_ : ¬ byz.isByzantine p.dst)
      (_ : let (st', msgs, (_int, _out)) := protocol.procMessage w.nodes (w.localState p.dst) p.src p.msg
          w' = { w with localState := updNS p.dst st' w.localState,
                        packetSoup := Packet.consume p w.packetSoup + msgs })

    /-- Node `proc` executes internal transition `t`. -/
    | intern (proc : NetAddr) (t : InternalEvent)
      (_ : s = step.intern proc t)
      (_ : ¬ byz.isByzantine proc)
      (_ : let (st', msgs, _evs) := protocol.procInternal w.nodes (w.localState proc) t
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
