# Veil: A Framework for Automated and Interactive Verification of Transition Systems (Artifact)

[CAV'25 submission #272](https://cav2025.hotcrp.com/paper/272)

Veil is a _foundational_ framework for (1) specifying, (2)
implementing, (3) testing, and (4) proving safety properties of state
transition systems, with a focus on distributed protocols.

Veil is embedded in the [Lean 4 proof assistant](https://lean-lang.org/)
and provides push-button verification for transition systems and their
properties expressed decidable fragments of first-order logic, with the
full power of a modern higher-order proof assistant for when automation
falls short.

Veil is licensed under the [Apache 2.0
license](https://www.apache.org/licenses/LICENSE-2.0) and is available
on GitHub at
[github.com/verse-lab/veil](https://github.com/verse-lab/veil).

## Requirements

We recommend running this artifact on a machine with at least 4 CPU
cores and at least 16 GB of RAM.

The artifact Docker image comes with all dependencies downloaded and
Veil already compiled (for archival purposes). Running the artifact
does not require an Internet connection. However, if you `lake clean`,
a further `lake build` will require an Internet connection.

Time required for various tasks is as follows:

- A full `lake build` from scratch (i.e. after a `lake clean`) takes
about 10 minutes, depending on the speed of your internet connection;

- With Veil already compiled, the smoke test `smoke_test.sh` should
take no more than 2-3 minutes; this runs the evaluation script (for
both Veil and Ivy) on a subset of smaller benchmarks;

- Running the evaluation script `evaluate_once.sh` (which runs a single
cycle of the full evaluation) takes around 30 minutes;

- Running the evaluation script `evaluate_all.sh` (which runs the full
evaluation, i.e. 5 repeats, averaging the results) takes around 2.5
hours.

We have tested this artifact on a 2024 MacBook Pro with an M4 processor
and 32 GB of RAM.

## Structure and Contents

The Docker image contains Veil's implementation in `/root/veil`, which
consists of four major directories and their subdirectories:

- `Veil/`: the implementation of Veil,
  - `DSL/`: Veil DSL
    - `Action/`: implementation of the imperative action DSL
      - `Syntax.lean`: syntax of imperative DSL
      - `Lang.lean`: expansion of syntax into the
      shallowly-embedded semantics
      - `Theory.lean`: semantics of action DSL with meta-theory
      and the soundness proof
    - `Specification/`: implementation of the specification DSL (i.e.
    state definitions, actions, invariants)
      - `Syntax.lean`: syntax of specification DSL
      - `Lang.lean`: expansion of syntax into the
      shallowly-embedded semantics
    - `Trace/`: the `sat trace` / `unsat trace` sub-DSL
    - `Check/`: `#check_invariants`, `prove_inv_inductive`, etc.
  - `SMT/`: tactics for interaction with SMT
  - `Tactic/`: auxiliary tactics for proof automation
- `Test/`: unit tests for main Veil features,
- `Benchmarks/`, with subdirectories:
  - `Benchmarks/Veil`: Veil's benchmarks used in the evaluation,
  consisting of realistic specifications of distributed protocols
    - in particular, `Benchmarks/Veil/SuzukiKasamiInts.lean` is the running
    example in the paper
    - all Veil benchmarks (except `ReliableBroadcast`, for which we
    wrote both Veil and Ivy specifications) have a comment at the
    beginning of the file indicating the source of the Ivy
    specification they were adapted from
  - `Benchmarks/Ivy`: Ivy benchmarks for the same protocols, as
  baselines
  - `Benchmarks/logs`: logs and results obtained when running the
  evaluation script on our machine
- `Tutorial/Ring.lean` is a heavily-commented **tutorial** example of
Veil, highlighting the main features of the framework

Ivy's sources from commit
[dbe45e7f](https://github.com/kenmcmil/ivy/commit/dbe45e7fc5769170b92492b70827d1cf7efb7972)
are in `/root/ivy`. This is pre-built and installed globally. Ivy ships
with its own version of Z3.

### Definitions and Theorems Highlighted in the Paper (Section 3)


### Case Studies Highlighted in the Paper (Section 4.3)

#### Stellar Consensus Protocol

This artifact includes the formalisation and verification of the
Stellar Consensus Protocol (SCP) in Veil, which is adapted from [the
work in this repository](https://github.com/stellar/scp-proofs) at
commit `3e0428acc78e598a227a866b99fe0b3ad4582914`.

The original work includes [an Ivy specification for
SCP](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy),
where the underlying system model is abstracted into several properties
in first-order logic stated using the language of Ivy (e.g.,
[`node_properties`](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy#L24-L29)
and
[`quorum_properties`](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/SCP.ivy#L31-L40));
these properties are then taken as assumptions by Ivy. The abstraction
is proven to be sound with regard to a more concrete higher-order
system model (concrete in the sense that concepts like quorums have
their own definitions, rather than axiomatised; higher-order in the
sense that those definitions may involve sets and quantifications over
sets) in [a separate Isabelle/HOL
file](https://github.com/stellar/scp-proofs/blob/3e0428acc78e598a227a866b99fe0b3ad4582914/FBA.thy).
For more details about the original work, please refer to [the
associated paper](https://doi.org/10.4230/OASICS.FMBC.2020.9).

- `Benchmarks/Veil/SCPTheory.lean` is adapted from the Isabelle/HOL
file mentioned above and includes the concrete system model;
- `Benchmarks/Veil/SCP.lean` is mainly adapted from the Ivy
specification, with an additional proof showing that the concrete model
satisfies the abstract model (i.e., the properties in first-order logic
abstracted from the concrete model).

#### Rabia Protocol

This artifact includes the formalisation and verification of the [Rabia
Protocol](https://doi.org/10.1145/3477132.3483582) in Veil, which is
adapted from [the work in this
repository](https://github.com/stellar/scp-proofs) at commit
`88013ca8369a7ae3adfed44e3c226c8d97f11209` (note that this commit is
not the latest commit for the repository, but the latest for the two
files mentioned below).

The original work includes [an Ivy specification for
Rabia](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/ivy/weak_mvc.ivy)
and [a separate Rocq
file](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/coq/weak_mvc.v).
The Rocq file is mainly for proving some additional invariants that
cannot be easily handled by Ivy. For more details about the original
work, please refer to the Section 5 of [the associated
paper](https://doi.org/10.1145/3477132.3483582).

- `Benchmarks/Veil/Rabia.lean` is adapted from the Ivy specification
mentioned above.

- `Benchmarks/Veil/RabiaMore.lean` is adapted from the Rocq file
mentioned above, with one major difference: the Rocq file take all
invariants checked by Ivy as axioms, while `RabiaMore.lean` *reuses*
the invariants checked in `Rabia.lean`.

**A Discrepancy in the Original Work** — we found that there is a
discrepancy for the invariant `started_pred` between [its statement in
the Ivy
spec](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/ivy/weak_mvc.ivy#L356)
and [its statement in the Rocq
file](https://github.com/haochenpan/rabia/blob/88013ca8369a7ae3adfed44e3c226c8d97f11209/proofs/coq/weak_mvc.v#L115-L116).
More precisely, its statement in the Ivy spec is a simple tautology,
while its statement in Rocq is non-trivial and should be regarded as
the correct formulation.


## Set Up and Smoke Test

The artifact for Veil is a x86 Ubuntu Docker image containing Lean
v4.16.0 along with Veil and its benchmark sets depicted in Figure 5,
and [Ivy](https://github.com/kenmcmil/ivy) for our baseline. For
convenience, the source code for Veil is also attached separate from
the Docker image.

In order to import the Docker container, run:

```bash
sudo docker load < veil_cav25.tar
```

Now, run Veil's basic sanity check using the following command:
```bash
sudo docker run -ti --rm veil:cav25 run_quick.sh
```
This should take less than a minute. The expected result is <TODO>

## Full Evaluation

For the full evaluation, run the following command:

```bash
sudo docker run -ti --rm veil:cav25 run_all.sh
```

This will take about <time>, and run both Veil and Ivy, printing a csv file summarizing the results. The expected results should correspond to the times in Figure 5 in the paper. Please be reminded that the graph is normalized and the real times are written above each bar.

It is also possible to run just Veil:

```bash
sudo docker run -ti --rm veil:cav25 run_all.sh --no-ivy
```
------

## Reusability Guide (Tutorial)

Veil is fully [open source](https://github.com/verse-lab/veil/) and
available freely under a permissive Apache 2.0 license.

The file `/root/Veil/Examples/Tutorial/Ring.lean` contains a guided
tour of Veil's main features. Check it out if you want to see what Veil
can do!

### Using Veil in your own project

To use `veil` in your project, add the following to your
`lakefile.lean`:

<TODO - how to require from folder>

```lean
require "verse-lab" / "veil" @ git "main"
```

Or add the following to your `lakefile.toml`:

```toml
[[require]]
name = "veil"
git = "https://github.com/verse-lab/veil.git"
rev = "main"
```


### Build

Veil requires [Lean 4](https://github.com/leanprover/lean4). We have tested Veil
on macOS (arm64) and Ubuntu (x86_64). Windows with WSL2 is also supported.
Native Windows support is not yet available.


To build Veil, run:

```bash
lake build
```

<!-- This will build the whole project, including the tests, but without the
case studies. -->


<details close>
<summary><strong>How to install Lean?</strong></summary>

If you don't have Lean installed, we recommend installing it via
[`elan`](https://github.com/leanprover/elan):


```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable
```

</details>

<details close>
<summary><strong>Dependencies</strong></summary>

Veil depends on [`z3`](https://github.com/Z3Prover/z3),
[`cvc5`](https://github.com/cvc5/cvc5), and
[`uv`](https://github.com/astral-sh/uv). You do not need to have these installed
on your system, as our build system will download them automatically when you
run `lake build`. Veil will use its own copies of these tools, and will not
touch your system-wide versions.

Note that if you want to invoke Lean-Auto's `auto` tactic, you need to have
`z3` and `cvc5` installed on your system and available in your PATH.
</details>

