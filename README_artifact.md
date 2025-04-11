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
Veil and Ivy already compiled (for archival purposes). Running the
artifact does not require an Internet connection. However, if you `lake
clean`, a further `lake build` will require an Internet connection.

Time required for various tasks is as follows:

- A full `lake build` from scratch (i.e. after a `lake clean`) takes
10-20 minutes, depending on the speed of your CPU and internet
connection;

- With Veil already compiled, the smoke test `smoke_test.sh` should
take no more than 2-3 minutes; this runs the evaluation script (for
both Veil and Ivy) on a subset of smaller benchmarks;

- Running the evaluation script `evaluate_once.sh` (which runs a single
cycle of the full evaluation) takes around 30 minutes;

- Running the evaluation script `evaluate_all.sh` (which runs the full
evaluation, i.e. 5 repeats, averaging the results) takes around 2.5
hours.

We have tested this artifact on a 2024 MacBook Pro with an M4 processor
and 32 GB of RAM and a Thinkpad X1 Carbon with a 13th Gen Intel(R)
Core(TM) i7-1370P processor and 64GB of RAM.

## Structure and Contents

The Docker image contains Veil's implementation in `/root/veil`, which
consists of four major directories and their subdirectories:

- `Veil/`: the implementation of Veil,
  - `Veil/Base.lean`: defines all the options for Veil
  - `DSL/`: Veil DSL
    - `Action/`: implementation of the imperative action DSL
      - `Syntax.lean`: syntax of imperative DSL
      - `Lang.lean`: expansion of syntax into the
      shallowly-embedded semantics
      - `Theory.lean`: semantics of action DSL with meta-theory
      and the soundness proof
    - `Specification/`: implementation of the specification DSL (i.e.
    state definitions, actions declarations, invariants)
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

All the following are found in `Veil/DSL/Action/Theory.lean`:

- `BigStep` - big-step semantics (lines 175-195)
  - note the `∃ s''` in the definition of `BigStep.bind` (line 178):

```lean
def BigStep.bind (act : BigStep σ ρ) (act' : ρ -> BigStep σ ρ') : BigStep σ ρ' :=
  fun s r' s' => ∃ r s'', act s r s'' ∧ act' r s'' r' s'
```

- `WP` - weakest precondition semantics (lines 85-125)
  - note there is no existential quantification in the definition of
  `WP.bind` (line 78):

```lean
def Wp.bind (wp : Wp m σ ρ) (wp_cont : ρ -> Wp m σ ρ') : Wp m σ ρ' :=
  fun s post => wp s (fun r s' => wp_cont r s' post)
```

- The definition of `tr'` in the paper is `Wp.toBigStep` (after
unfolding `Wp.toWlp`) (lines 234-236):

```lean
def Wp.toBigStep {σ} (wp : Wp m σ ρ) : BigStep σ ρ :=
  fun s r' s' =>
    wp.toWlp s (fun r₀ s₀ => r' = r₀ ∧ s' = s₀)
```

- `big_step_to_wp` (line 438) is the soundness theorem in Section 3.2:

```lean
theorem big_step_to_wp (act : Wp m σ ρ) [LawfulAction act] (req : SProp σ) :
  act.alwaysSuccessfullyTerminates req ->
  req s ->
  act s = act.toBigStep.toWp s
```

For this theorem `alwaysSuccessfullyTerminates` encodes that the action
has no failing assertions (when executed from a state `s` satisfying
some precondition `req` — this is usually instantiated with either
`True` or the inductive invariant).

`LawfulAction`, defined in lines 335-340, encodes the properties
necessary for this conversion to be sound. The typeclass instances in
`section LawfulActionInstances` (lines 452-541) show that all of our
actions satisfy these properties.

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

Then you can obtain a shell into the container by running:

```bash
docker run -it --platform linux/amd64 --volume ./container-output:/tmp/output veil:cav25 /bin/bash --login
```

This will mount the `./container-output` directory on your machine as
`/tmp/output` inside the container. Within the container, any files you
place in `/tmp/output` will be visible on your host machines. All
output files from our evaluation scripts are automatically copied to
this directory.

Now, run Veil's basic sanity check using the following command:
```bash
sh smoke_test.sh
```

This should take no more than 2-3 minutes. 

It will produce a number of files:

- `smoke_test_log.txt` - full log of the output from Ivy and Veil's
profiling of `#check_invariants`, used to compute the numbers in the
figure in the paper

- `smoke_test_results.txt` - a copy of what's displayed in the terminal
as the evaluation script runs; Ivy timeouts get a `total_ivy_time`
of 0.0

- `smoke_test_results.json` - a JSON version of the above; this can be
used to reproduce the figures by running:

```bash
python3 scripts/eval.py evaluate_all_results.json --output-file fig.pdf
```

- `smoke_test_raw.pdf` - the raw figure, without normalizing the times
to Veil's runtime

- `smoke_test_normalized.pdf` - the normalized figure, similar to what
we show in the paper (Fig. 5); note that the actual runtimes are
written on top of the bars (normalization is only for sizing the bars)

## Full Evaluation

For the full evaluation, run the following command:

```bash
sh evaluate_all.sh
```

This will take about 2.5 hours, and run both Veil and Ivy, generating
the same files as the smoke test, but with prefix `evaluate_all_` and
with the full set of benchmarks.

`evaluate_all_normalized.pdf` should correspond to Figure 5 in the
paper. Note that your execution times may differ from ours, but the
overall shape of the bars should roughly match. Please be reminded that
the graph is normalized and the real times are written above each bar.

### Recreating the Exact Figure 5 in the Paper

We have attached the logs of our execution in `logs/`. You can recreate
the Figure 5 used in the paper from our execution results by running:

```bash
python3 scripts/eval.py ./logs/evaluate_all_results.json --output-file fig.pdf
```

## Badge Checklist

### Functional

- **(Documentation)** Veil is well-documented, includes a tutorial
(`Tutorial/Ring.lean`) and a number of examples for users to take as
inspiration when writing their own specifications. The source code is
reasonably organised into sub-modules, and sub-components (e.g. clear
split between syntax and semantics of the different sub-DSLS) and has
extensive comments (e.g. in `Veil/DSL/Action/Theory.lean`). Most syntax
constructs have detailed doc-comments that show up on hover in Visual
Studio Code and other similar IDEs.

- **(Completeness)** The Suzuki Kasami Ints example in the paper,
including the BMC queries and the interactive proof, are found in
`Benchmarks/Veil/SuzukiKasamiInts.lean`. The definitions and theorems
in Section 3 are present in `Veil/DSL/Action/Theory.lean` and the main
ones are highlighted in this README ("Definitions and Theorems
Highlighted in the Paper (Section 3)"). All the benchmarks mentioned in
the paper (Section 4.1) are present in the artifact. There is an
evaluation script (`evaluate_all.sh`) to directly reproduce the figure
in the paper. Moreover, the log information from the execution that
generated the exact figure in the paper is included in the artifact,
and the Figure 5 in the paper can be reproduced automatically (via
`scripts/eval.py` as mentioned above) from the build log. The two case
studies in Section 4.3 (Stellar Consensus Protocol and Rabia) are
present and highlighted in this README. The discrepancy in Rabia
mentioned in the paper is highlighted in this README.

- **(Consistency)** The artifact supports the claims made in the paper.
Whilst execution times on other machines may differ from ours, the
execution logs and scripts used to produce the exact figure in the
paper are present in the artifact. Note also that we do not make
specific performance claims in the paper besides the claim that Veil's
"automated verification performance is acceptable for practical
verification tasks" (in the abstract).

- **(Correctness)** Veil employs software engineering practices such as
unit testing, and comes with a soundness proof for part of its
functionality. Moreover, we tested Veil against Ivy — the reference
tool for this domain — for a fairly extensive benchmark set and
obtained (ignoring Ivy's timeouts) consistent results.

### Reusable

- **(License)** Veil is licensed under the Apache 2.0 license, which is
an open-source permissive license that allows reuse and repurposing,
including for commercial purposes. Our dependencies (Lean 4,
`mathlib4`, `lean-smt`, and `lean-auto`) are licensed under the same
permissive license.

- **(Dependencies)** We use recent versions of our dependencies, i.e.
the latest (as of the time of writing this artifact README) versions of
`lean-smt` and `lean-auto`, and the latest Lean 4 version they are
compatible with, i.e. Lean v4.16.0, originally released on 2025-02-03.
All dependencies are clearly defined in `lakefile.lean`.

- **(Reusability beyond the paper)** Users can use Veil to verify their
own specifications, as detailed in the Reusability Guide below (adapted
from Veil's `README`). Veil can be used in other Lean projects by
simply including it in the `lakefile.lean` and issuing an `import Veil`
command in an open Lean file. We encourage users read through the
tutorial and look at the examples to learn what Veil specifications
look like and what features are available.

- **(Extensions)** The artifact is open-source.

- **(Use outside the container)** Absolutely. The only hard dependency
for Veil is Lean itself (every other dependency, including CVC5 and Z3,
is downloaded at build time), which can be installed on any modern
system as detailed below by running the following command:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable
```

Moreover, opening the Veil repository in a Visual Studio Code window
with the [Lean 4
extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
installed is sufficient to fully build Veil — no command-line
installation is necessary.

In fact, we recommend people who are reviewing Veil for purposes other
than replicating Figure 5 in the paper to not use the artifact, but
rather simply clone Veil's public repository
(https://github.com/verse-lab/veil) and open it in a Visual Studio Code
window with the Lean 4 extension installed.

## Reusability Guide

Veil is fully [open source](https://github.com/verse-lab/veil/) and
available freely under a permissive Apache 2.0 license.

Veil is a _foundational_ framework for (1) specifying, (2)
implementing, (3) testing, and (4) proving safety (and, in the future,
liveness) properties of state transition systems, with a focus on
distributed protocols.

Veil is embedded in the [Lean 4 proof
assistant](https://lean-lang.org/) and provides push-button
verification for transition systems and their properties expressed
decidable fragments of first-order logic, with the full power of a
modern higher-order proof assistant for when automation falls short.

## Using `veil`

To use `veil` in your project, add the following to your
`lakefile.lean`:

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

See
[`verse-lab/veil-usage-example`](https://github.com/verse-lab/veil-usage-example)
for a fully set-up example project that you can
[use as a template](https://github.com/new?template_name=veil-usage-example&template_owner=verse-lab).

## Tutorial

The file
[`Examples/Tutorial/Ring.lean`](https://github.com/verse-lab/veil/blob/main/Examples/Tutorial/Ring.lean)
contains a guided tour of Veil's main features. Check it out if you want to see
what Veil can do!

## Build

Veil requires [Lean 4](https://github.com/leanprover/lean4). We have tested Veil
on macOS (arm64) and Ubuntu (x86_64). Windows with WSL2 is also supported.
Native Windows support is not yet available.


To build Veil, run:

```bash
lake build
```

<!-- This will build the whole project, including the tests, but without the
case studies. -->

To build the case studies run:

```bash
lake build Examples
```

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
