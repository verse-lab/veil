# Stellar Consensus Protocol in Veil

This directory includes the formalisation and verification of the Stellar Consensus Protocol (SCP) in Veil, which is adapted from [the work in this repository](https://github.com/stellar/scp-proofs) at commit `3e0428acc78e598a227a866b99fe0b3ad4582914`. 

The original work includes [an Ivy specification for SCP](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy), where the underlying system model is abstracted into several properties in first-order logic stated using the language of Ivy (e.g., [`node_properties`](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy#L24-L29) and [`quorum_properties`](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy#L31-L40)); these properties are then taken as assumptions by Ivy. The abstraction is proven to be sound with regard to a more concrete higher-order system model (concrete in the sense that concepts like quorums have their own definitions, rather than axiomatised; higher-order in the sense that those definitions may involve sets and quantifications over sets) in [a separate Isabelle/HOL file](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/FBA.thy). For more details about the original work, please refer to [the associated paper](https://doi.org/10.4230/OASICS.FMBC.2020.9). 

## File Organisation

- `SCPTheory.lean` is adapted from the Isabelle/HOL file mentioned above and includes the concrete system model. 
- `SCP.lean` is mainly adapted from the Ivy specification, with an additional proof showing that the concrete model satisfies the abstract model (i.e., the properties in first-order logic abstracted from the concrete model). 
