# Rabia Protocol in Veil

This directory includes the formalisation and verification of the [Rabia Protocol](https://doi.org/10.1145/3477132.3483582) in Veil, which is adapted from [the work in this repository](https://github.com/stellar/scp-proofs) at commit `88013ca8369a7ae3adfed44e3c226c8d97f11209` (note that this commit is not the latest commit for the repository, but the latest for the two files mentioned below). 

The original work includes [an Ivy specification for Rabia](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/ivy/weak_mvc.ivy) and [a separate Rocq file](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/coq/weak_mvc.v). The Rocq file is mainly for proving some additional invariants that cannot be easily handled by Ivy. For more details about the original work, please refer to the Section 5 of [the associated paper](https://doi.org/10.1145/3477132.3483582). 

## File Organisation

- `Rabia.lean` is adapted from the Ivy specification mentioned above. 
- `RabiaMore.lean` is adapted from the Rocq file mentioned above, with one major difference: the Rocq file take all invariants checked by Ivy as axioms, while `RabiaMore.lean` *reuses* the invariants checked in `Rabia.lean`. 

## A Discrepancy in the Original Work

We found that there is a discrepancy for the invariant `started_pred` between [its statement in the Ivy spec](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/ivy/weak_mvc.ivy#L356) and [its statement in the Rocq file](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/coq/weak_mvc.v#L115-L116). More precisely, its statement in the Ivy spec is a simple tautology, while its statement in Rocq is non-trivial and should be regarded as the correct formulation. 
