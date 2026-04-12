------------------------- MODULE German -------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

\* Source: https://github.com/egolf-cs/scythe-fmcad2024/blob/main/run_tool/sketches/German.tla

\* 
\* 
\* Specification of German cache coherence protocol.
\* 
\* Based on the Murphi model given in:
\* 
\* Chou, CT., Mannava, P.K., Park, S. (2004). 
\* A Simple Method for Parameterized Verification of Cache Coherence Protocols. 
\* In: Hu, A.J., Martin, A.K. (eds) Formal Methods in Computer-Aided Design. FMCAD 2004. 
\* Lecture Notes in Computer Science, vol 3312. Springer, Berlin, Heidelberg. https://doi.org/10.1007/978-3-540-30494-4_27
\* 
\* 
\* See also related CAV 2015 MSI model here: https://github.com/abhishekudupa/kinara/blob/6e465ac41fc995f0df726dc2c5b73e3ba4a7775b/test/mc/MSI.cpp
\* 

CONSTANT NODE
CONSTANT DATA

CACHE_STATE == {"I", "S", "E"}
MSG_CMD == {"Empty", "ReqS", "ReqE", "Inv", "InvAck", "GntS", "GntE"}

CACHE == [State: CACHE_STATE, Data: DATA]
MSG == [Cmd: MSG_CMD, Data: DATA]

VARIABLES
    Cache,  \* array [NODE] of CACHE
    Chan1,  \* array [NODE] of MSG, channels for Req*
    Chan2,  \* array [NODE] of MSG, channels for Gnt* and Inv
    Chan3,  \* array [NODE] of MSG, channels for InvAck
    InvSet, \* array [NODE] of BOOLEAN, nodes to be invalidated
    ShrSet, \* array [NODE] of BOOLEAN, nodes having S or E copies
    ExGntd, \* BOOLEAN, E copy has been granted
    CurCmd, \* MSG_CMD, current request command
    CurPtr, \* NODE, current request node
    MemData,\* DATA, memory data
    AuxData \* DATA, latest value of cache line

vars == <<Cache, Chan1, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

Init ==
    /\ Cache = [i \in NODE |-> [State |-> "I", Data |-> 1]]
    /\ Chan1 = [i \in NODE |-> [Cmd |-> "Empty", Data |-> 1]]
    /\ Chan2 = [i \in NODE |-> [Cmd |-> "Empty", Data |-> 1]]
    /\ Chan3 = [i \in NODE |-> [Cmd |-> "Empty", Data |-> 1]]
    /\ InvSet = [i \in NODE |-> FALSE]
    /\ ShrSet = [i \in NODE |-> FALSE]
    /\ ExGntd = FALSE
    /\ CurCmd = "Empty"
    /\ CurPtr \in NODE
    /\ MemData = 1
    /\ AuxData = 1

TypeInvariant ==
    /\ Cache \in [NODE -> CACHE]
    /\ Chan1 \in [NODE -> MSG]
    /\ Chan2 \in [NODE -> MSG]
    /\ Chan3 \in [NODE -> MSG]
    /\ InvSet \in [NODE -> BOOLEAN]
    /\ ShrSet \in [NODE -> BOOLEAN]
    /\ ExGntd \in BOOLEAN
    /\ CurCmd \in MSG_CMD
    /\ CurPtr \in NODE
    /\ MemData \in DATA
    /\ AuxData \in DATA

(* Define state transitions here, following the Murphi model *)
SendReqS(i) ==
    /\ Chan1[i].Cmd = "Empty"
    /\ Cache[i].State = "I"
    /\ Chan1' = [Chan1 EXCEPT ![i].Cmd = "ReqS"]
    /\ UNCHANGED <<Cache, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

SendReqE(i) ==
    /\ Chan1[i].Cmd = "Empty"
    /\ (Cache[i].State = "I" \/ Cache[i].State = "S")
    /\ Chan1' = [Chan1 EXCEPT ![i].Cmd = "ReqE"]
    /\ UNCHANGED <<Cache, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

RecvReqS(i) ==
    /\ CurCmd = "Empty"
    /\ Chan1[i].Cmd = "ReqS"
    /\ CurCmd' = "ReqS"
    /\ CurPtr' = i
    /\ Chan1' = [Chan1 EXCEPT ![i].Cmd = "Empty"]
    /\ InvSet' = [j \in NODE |-> ShrSet[j]]
    /\ UNCHANGED <<Cache, Chan2, Chan3, ShrSet, ExGntd, MemData, AuxData>>

RecvReqE(i) ==
    /\ CurCmd = "Empty"
    /\ Chan1[i].Cmd = "ReqE"
    /\ CurCmd' = "ReqE"
    /\ CurPtr' = i
    /\ Chan1' = [Chan1 EXCEPT ![i].Cmd = "Empty"]
    /\ InvSet' = [j \in NODE |-> ShrSet[j]]
    /\ UNCHANGED <<Cache, Chan2, Chan3, ShrSet, ExGntd, MemData, AuxData>>

SendInv(i) ==
    /\ Chan2[i].Cmd = "Empty"
    /\ InvSet[i] = TRUE
    /\ (CurCmd = "ReqE" \/ (CurCmd = "ReqS" /\ ExGntd = TRUE))
    /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Inv"]
    /\ InvSet' = [InvSet EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<Cache, Chan1, Chan3, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

SendInvAck(i) ==
    /\ Chan2[i].Cmd = "Inv"
    /\ Chan3[i].Cmd = "Empty"
    /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
    /\ Chan3' = [Chan3 EXCEPT ![i] = [Cmd |-> "InvAck", Data |-> IF Cache[i].State = "E" THEN Cache[i].Data ELSE Chan3[i].Data]]
    /\ Cache' = [Cache EXCEPT ![i].State = "I"]
    /\ UNCHANGED <<Chan1, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

RecvInvAck(i) ==
    /\ Chan3[i].Cmd = "InvAck"
    /\ CurCmd /= "Empty"
    /\ Chan3' = [Chan3 EXCEPT ![i].Cmd = "Empty"]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = FALSE]
    /\ IF ExGntd = TRUE
       THEN /\ ExGntd' = FALSE
            /\ MemData' = Chan3[i].Data
       ELSE /\ UNCHANGED ExGntd
            /\ UNCHANGED MemData
    /\ UNCHANGED <<Cache, Chan1, Chan2, InvSet, CurCmd, CurPtr, AuxData>>

SendGntS(i) ==
    /\ CurCmd = "ReqS"
    /\ CurPtr = i
    /\ Chan2[i].Cmd = "Empty"
    /\ ExGntd = FALSE
    /\ Chan2' = [Chan2 EXCEPT ![i] = [Cmd |-> "GntS", Data |-> MemData]]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = TRUE]
    /\ CurCmd' = "Empty"
    /\ UNCHANGED <<Cache, Chan1, Chan3, InvSet, CurPtr, ExGntd, MemData, AuxData>>

SendGntE(i) ==
    /\ CurCmd = "ReqE"
    /\ CurPtr = i
    /\ Chan2[i].Cmd = "Empty"
    /\ ExGntd = FALSE
    /\ \A j \in NODE : ShrSet[j] = FALSE
    /\ Chan2' = [Chan2 EXCEPT ![i] = [Cmd |-> "GntE", Data |-> MemData]]
    /\ ShrSet' = [ShrSet EXCEPT ![i] = TRUE]
    /\ ExGntd' = TRUE
    /\ CurCmd' = "Empty"
    /\ UNCHANGED <<Cache, Chan1, Chan3, InvSet, CurPtr, MemData, AuxData>>

RecvGntS(i) ==
    /\ Chan2[i].Cmd = "GntS"
    /\ Cache' = [Cache EXCEPT ![i] = [State |-> "S", Data |-> Chan2[i].Data]]
    /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
    /\ UNCHANGED <<Chan1, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

RecvGntE(i) ==
    /\ Chan2[i].Cmd = "GntE"
    /\ Cache' = [Cache EXCEPT ![i] = [State |-> "E", Data |-> Chan2[i].Data]]
    /\ Chan2' = [Chan2 EXCEPT ![i].Cmd = "Empty"]
    /\ UNCHANGED <<Chan1, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData, AuxData>>

Store(i, d) ==
    /\ Cache[i].State = "E"
    /\ Cache' = [Cache EXCEPT ![i].Data = d]
    /\ AuxData' = d
    /\ UNCHANGED <<Chan1, Chan2, Chan3, InvSet, ShrSet, ExGntd, CurCmd, CurPtr, MemData>>

Next ==
    \/ \E i \in NODE : SendReqS(i)
    \/ \E i \in NODE : SendReqE(i)
    \/ \E i \in NODE : RecvReqS(i)
    \/ \E i \in NODE : RecvReqE(i)
    \/ \E i \in NODE : SendInv(i)
    \/ \E i \in NODE : SendInvAck(i)
    \/ \E i \in NODE : RecvInvAck(i)
    \/ \E i \in NODE : SendGntS(i)
    \/ \E i \in NODE : SendGntE(i)
    \/ \E i \in NODE : RecvGntS(i)
    \/ \E i \in NODE : RecvGntE(i)
    \/ \E i \in NODE : \E d \in DATA : Store(i, d)

Fairness == 
    /\ \A i \in NODE : WF_vars(SendReqS(i))
    /\ \A i \in NODE : SF_vars(SendReqE(i))
    /\ \A i \in NODE : WF_vars(RecvReqS(i))
    /\ \A i \in NODE : SF_vars(RecvReqE(i))
    /\ \A i \in NODE : WF_vars(SendInv(i))
    /\ \A i \in NODE : WF_vars(SendInvAck(i))
    /\ \A i \in NODE : WF_vars(RecvInvAck(i))
    /\ \A i \in NODE : WF_vars(SendGntS(i))
    /\ \A i \in NODE : SF_vars(SendGntE(i))
    /\ \A i \in NODE : WF_vars(RecvGntS(i))
    /\ \A i \in NODE : SF_vars(RecvGntE(i))
    \* I don't think fairness requirements are needed on Store
    \* in order to satisfy either LivenessExclusive or LivenessShared.
    \* Adding more fairness constraints seems to slow down TLC, so omit it for now.
    \* /\ \A i \in NODE : \A d \in DATA : WF_vars(Store(i, d))

Spec == Init /\ [][Next]_vars /\ Fairness

\* 
\* Safety properties.
\* 

CtrlProp ==
    \A i, j \in NODE :
        i /= j =>
            /\ (Cache[i].State = "E" => Cache[j].State = "I")
            /\ (Cache[i].State = "S" => (Cache[j].State = "I" \/ Cache[j].State = "S"))

DataProp ==
    /\ (ExGntd = FALSE => MemData = AuxData)
    /\ \A i \in NODE :
        Cache[i].State /= "I" => Cache[i].Data = AuxData

Invariant ==
    /\ CtrlProp
    /\ DataProp

\* 
\* Liveness properties. 
\* 
\* For now we just check LivenessExclusive, which seems a reasonable start to get synthesis going.
\* 

\* Liveness property: any outstanding exclusive request is eventually granted.
\* LivenessExclusive ==
\*     \A i \in NODE : []((Chan1[i].Cmd = "ReqE") ~> (Chan2[i].Cmd = "GntE"))

\* \* Liveness property: any outstanding shared request is eventually granted.
\* LivenessShared ==
\*     \A i \in NODE :
\*         [](Chan1[i].Cmd = "ReqS" => <>(Chan2[i].Cmd = "GntS"))

\* Symmetry == Permutations(NODE)

====