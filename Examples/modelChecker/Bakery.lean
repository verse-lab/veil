import Veil
import Veil.Frontend.DSL.Action.Extraction.Extract
import Veil.Core.Tools.Checker.Concrete.Main

import Veil.Core.Tools.Checker.Concrete.modelCheckerView
import ProofWidgets.Component.HtmlDisplay

veil module SimpleAllocator
-- ------------------------ MODULE SimpleAllocator -------------------------
-- (***********************************************************************)
-- (* Specification of an allocator managing a set of resources:          *)
-- (* - Clients can request sets of resources whenever all their previous *)
-- (*   requests have been satisfied.                                     *)
-- (* - Requests can be partly fulfilled, and resources can be returned   *)
-- (*   even before the full request has been satisfied. However, clients *)
-- (*   only have an obligation to return resources after they have       *)
-- (*   obtained all resources they requested.                            *)
-- (***********************************************************************)
-- https://github.com/tlaplus/Examples/blob/master/specifications/allocator/SimpleAllocator.tla

-- EXTENDS FiniteSets, TLC

-- CONSTANTS
--   Clients,     \* set of all clients
--   Resources    \* set of all resources
type client
type resource
immutable relation Clients : client → Bool
immutable relation Resources : resource → Bool
-- ASSUME
--   IsFiniteSet(Resources)

-- VARIABLES
--   unsat,       \* set of all outstanding requests per process
--   alloc        \* set of resources allocated to given process
relation unsatisfy : client → resource → Bool
relation alloc : client → resource → Bool
-- TypeInvariant ==
--   /\ unsat \in [Clients -> SUBSET Resources]
--   /\ alloc \in [Clients -> SUBSET Resources]

-- -------------------------------------------------------------------------
#gen_state
assumption [fixed_clients_set] ∀c, Clients c
assumption [finite_resources] ∀s, Resources s


after_init {
  unsatisfy C R := false
  alloc C R := false
}


action Request (c : client) (s : resource) {
  require ∀r, ¬ unsatisfy c r
  require ∀r, ¬ alloc c r
  -- require ¬ S # {}
  unsatisfy c s := true
}


action Allocate (c : client) (s : resource) {
  require unsatisfy c s ∧ (Resources s ∧ ∀c', ¬ alloc c' s)
  -- Introduce an error here, originally is unsatisfy c s ∧ (Resources s ∧ ∀c', ¬ alloc c' s)
  alloc c s := true
  unsatisfy c s := false
}


action Return (c : client) (s : resource) {
  require alloc c s
  alloc c s := false
}

-- -------------------------------------------------------------------------

-- (* The complete high-level specification. *)
-- SimpleAllocator ==
--   /\ Init /\ [][Next]_vars
--   /\ \A c \in Clients: WF_vars(Return(c, alloc[c]))
--   /\ \A c \in Clients: SF_vars(\E S \in SUBSET Resources: Allocate(c,S))

-- -------------------------------------------------------------------------

-- ResourceMutex ==
--   \A c1,c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}
invariant [resource_mutex] ∀c1 c2, c1 ≠ c2 → ¬(∃s, alloc c1 s ∧ alloc c2 s)
-- ClientsWillReturn ==
--   \A c \in Clients : unsat[c]={} ~> alloc[c]={}
-- ClientsWillObtain ==
--   \A c \in Clients, r \in Resources : r \in unsat[c] ~> r \in alloc[c]
-- InfOftenSatisfied ==
--   \A c \in Clients : []<>(unsat[c] = {})

-- -------------------------------------------------------------------------

-- (* Used for symmetry reduction with TLC *)
-- Symmetry == Permutations(Clients) \cup Permutations(Resources)

-- -------------------------------------------------------------------------

-- (* The following version states a weaker fairness requirement for the  *)
-- (* clients: resources need be returned only if the entire request has  *)
-- (* been satisfied.                                                     *)

-- SimpleAllocator2 ==
--   /\ Init /\ [][Next]_vars
--   /\ \A c \in Clients: WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
--   /\ \A c \in Clients: SF_vars(\E S \in SUBSET Resources: Allocate(c,S))

#gen_spec
-- #check_invariants

-- -------------------------------------------------------------------------

-- THEOREM SimpleAllocator => []TypeInvariant
-- THEOREM SimpleAllocator => []ResourceMutex
-- THEOREM SimpleAllocator => ClientsWillReturn
-- THEOREM SimpleAllocator2 => ClientsWillReturn
-- THEOREM SimpleAllocator => ClientsWillObtain
-- THEOREM SimpleAllocator => InfOftenSatisfied
-- (** The following do not hold:                          **)
-- (** THEOREM SimpleAllocator2 => ClientsWillObtain       **)
-- (** THEOREM SimpleAllocator2 => InfOftenSatisfied       **)
-- =========================================================================
#prepareExecution

#finitizeTypes (Fin 5), (Fin 3)




def view (st : StateConcrete) := hash st
def detect_prop : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => resource_mutex ρ σ)
def terminationC : TheoryConcrete → StateConcrete → Bool := (fun ρ σ => true)
def cfg : TheoryConcrete := default


def modelCheckerResult' := (runModelCheckerx initVeilMultiExecM nextVeilMultiExecM labelList detect_prop terminationC cfg view).snd
def statesJson : Lean.Json := Lean.toJson (recoverTrace initVeilMultiExecM nextVeilMultiExecM cfg (collectTrace' modelCheckerResult'))
#eval modelCheckerResult'.seen.size
open ProofWidgets
open scoped ProofWidgets.Jsx
#html <ModelCheckerView trace={statesJson} layout={"vertical"} />

end SimpleAllocator
