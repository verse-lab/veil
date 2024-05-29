import Mathlib.Tactic
import LeanSts.BFT.Byzantine

class NetworkPacket {NetAddr Message Packet : Type} :=
  src : Packet → NetAddr
  dst : Packet → NetAddr
  msg : Packet → Message

class NetworkProtocol {NetAddr Message Packet LocalState InternalTransition : Type} :=
  localInit : NetAddr → LocalState
  procInternal : LocalState → InternalTransition → LocalState × List Packet
  procMessage : LocalState → NetAddr /- sender -/ → Message → LocalState × List Packet

/-- A network consists of the packet soup and the local states of nodes.
  Informally, this is called a "World". -/
structure NetworkState {NetAddr Packet LocalState : Type} :=
  /-- The respective local state of nodes. -/
  localState : NetAddr → LocalState
  /-- The set of sent messages. -/
  packetSoup : Multiset Packet

theorem defaultNetworkState
  [protocol : @NetworkProtocol NetAddr Message Packet LocalState InternalTransition]
  : Inhabited (@NetworkState NetAddr Packet LocalState) :=
  ⟨{ localState := λ n => protocol.localInit n, packetSoup := ∅ }⟩

structure AsynchronousNetwork {NetAddr Message Packet LocalState InternalTransition : Type}
  [pkt : @NetworkPacket NetAddr Message Packet]
  [protocol : @NetworkProtocol NetAddr Message Packet LocalState InternalTransition]
  [byz : @ByzantineAdversary NetAddr Message (@NetworkState NetAddr Packet LocalState)] :=

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
    [pkt : @NetworkPacket NetAddr Message Packet]
    [protocol : @NetworkProtocol NetAddr Message Packet LocalState InternalTransition]
    [byz : @ByzantineAdversary NetAddr Message (@NetworkState NetAddr Packet LocalState)]
    (s : @step NetAddr Message Packet InternalTransition) (w w' : @World NetAddr Packet LocalState)
    | idle (_ : s = step.idle) (_ : w = w')
    | deliver (p : Packet)
      (_ : s = step.deliver p)
      (_ : p ∈ w.packetSoup)
      (_ : ¬ byz.setting.isByzantine (pkt.dst p) w)


#check AsynchronousNetwork
