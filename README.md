# Veil: A Multi-Modal Verifier for Transition Systems

<!-- [![Actions status](https://github.com/verse-lab/veil/actions/workflows/ci.yml/badge.svg)](https://github.com/verse-lab/veil/actions) -->
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
<a href="https://leanprover.zulipchat.com/#narrow/channel/537982-Veil"><img src="https://img.shields.io/badge/zulip-join_chat-brightgreen.svg" /></a>

Veil is a _foundational_ framework for (1) specifying, (2)
implementing, (3) model-checking, and (4) proving safety and liveness properties of state transition systems, with a focus on distributed protocols.

Veil is embedded in the [Lean 4 proof assistant](https://lean-lang.org/) and provides push-button
verification for transition systems and their properties expressed in
decidable fragments of first-order logic, with the full power of a
modern higher-order proof assistant for when automation falls short.

[Website](https://veil.dev/) · [Online playground](https://try.veil.dev/)

## Veil 2.0

This is Veil 2.0, the second major version of Veil. Veil 1.0 is available
under the tag [`v1.0.0`](https://github.com/verse-lab/veil/tree/v1.0.0).

If you encounter issues, please [report them to
us](https://github.com/verse-lab/veil/issues/new). You can ask questions on the
[Veil channel](https://leanprover.zulipchat.com/#narrow/channel/537982-Veil) on
the Lean Zulip, and we will be happy to answer.

## Learn Veil

Start with the extensively commented walkthroughs in
[Examples/Tutorial](Examples/Tutorial):

- [Examples/Tutorial/Ring.lean](Examples/Tutorial/Ring.lean) — the Ring Leader
  Election protocol, introducing Veil's syntax and its main commands
  (`#check_invariants`, `#model_check`, `sat`/`unsat trace`).

- [Examples/Tutorial/FloodSet.lean](Examples/Tutorial/FloodSet.lean) — a
  complete walkthrough of Veil's multi-modal workflow via the FloodSet
  synchronous crash-fault agreement protocol: modelling, testing via concrete and
  symbolic model checking, counterexample-driven invariant discovery, and an
  interactive Lean proof

These files are also available in the [online playground](https://try.veil.dev/), under the Examples button.

For liveness, [Examples/Demo/FloodSet/FloodSetLiveness.lean](Examples/Demo/FloodSet/FloodSetLiveness.lean)
adds temporal properties to the FloodSet protocol, model checks them with
`#temporal_check`, and proves one of them with `prove_temporal_by`.

The [docs/](docs/) directory documents the Veil DSL and its tools:

- [DSL-Reference.md](docs/DSL-Reference.md) — the constructs of the Veil DSL
  and its commands.
- [Distributed-DSL.md](docs/Distributed-DSL.md) — message-passing protocols
  written as the program each node runs, connected by a network with chosen assumptions.
- [ModelChecker-Guide.md](docs/ModelChecker-Guide.md) — explicit-state model
  checking with `#model_check`.
- [TemporalChecker-Guide.md](docs/TemporalChecker-Guide.md) — model checking
  temporal properties with `#temporal_check`.
- [Synthesizer-Guide.md](docs/Synthesizer-Guide.md) — invariant synthesis
  with `#updr`.

## Examples

Other examples in [Examples/](Examples/) are organised as follows:

| Directory | Contents |
| --- | --- |
| [TLA/](Examples/TLA/) | Translations and adaptations of TLA+ specifications. |
| [Ivy/](Examples/Ivy/) | Ivy-style first-order protocol models. |
| [Synchronous/](Examples/Synchronous/) | Synchronous consensus protocols with crash faults. |
| [Simulate/](Examples/Simulate/) | Simulation testing examples using `#simulate`. |
| [Puzzles/](Examples/Puzzles/) | State-machine models of recreational puzzles. |
| [AWS/](Examples/AWS/) | Buggy and fixed models of an AWS DNS race. |
| [StellarConsensus/](Examples/StellarConsensus/) | The Stellar Consensus Protocol and its supporting theory. |
| [Liveness/](Examples/Liveness/) | Temporal properties proved with `prove_temporal_by`. |
| [LivenessMC/](Examples/LivenessMC/) | Temporal properties model checked with `#temporal_check`, including TLA+ specifications and CAVA benchmarks. |
| [Demo/](Examples/Demo/) | Standalone demos: FloodSet, including its temporal properties, and the Ring protocol in three encodings. |

## Build

Install the system dependencies for your platform, then follow the shared setup
instructions below.

### 1. Install system dependencies

<details>
<summary>Ubuntu/Debian</summary>

```bash
sudo apt-get update &&
sudo apt-get install -y --no-install-recommends \
  ca-certificates curl git unzip clang lld libc++-dev libc++abi-dev
```

</details>

<details>
<summary>macOS</summary>

Install the XCode Command Line Tools (they provide `clang` and `git`):

```bash
xcode-select --install
```

</details>

### 2. Install Lean

On both Linux and macOS, install [Lean 4](https://github.com/leanprover/lean4)
through [Elan](https://github.com/leanprover/elan). Elan will
install the Lean version specified in `lean-toolchain` when you first run
`lake` in the repository:

```bash
set -o pipefail &&
(curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none) &&
. "$HOME/.elan/env"
```

### 3. Clone and build Veil

Clone Veil, enter the repository, and build it:

```bash
git clone https://github.com/verse-lab/veil.git
cd veil
lake build
```

### Prebuilt releases

For tagged releases, `lake build` automatically uses prebuilt artifacts for
Linux x86-64 and macOS ARM64 when available, falling back to a source build
otherwise. Dependencies may still need to compile.

### Troubleshooting

**(NPM errors)** npm is only needed when building modified widgets; see
[widget development](widget/README.md).

**(cvc5 errors)** If you see an error about `cvc5`, run:

```bash
rm -rf .lake/packages/cvc5
lake build
```

There is a sporadic issue in the build process for
[`lean-cvc5`](https://github.com/abdoo8080/lean-cvc5). Trying to build again
often fixes the problem.

## VS Code extension (optional)

The [Veil Verifier extension](https://marketplace.visualstudio.com/items?itemName=verse-lab.veil-verifier) provides an optional
VS Code interface for safety model checking with `#model_check`: creating
model-checking configurations, running model checkers, tracking progress, and
inspecting counterexamples. It works alongside the Lean 4 extension.
Veil's verification and model-checking commands can be used without this
extension.

See the [extension README](editors/vscode/README.md) for installation
and usage instructions.

## Agent skills

[.agents/skills/](.agents/skills/) holds skills for AI coding agents. Claude
Code loads them automatically in this repository (through `.claude/skills`).
To use one in your own project, copy or link its directory into your agent's
skills directory.

- [tla-to-veil](.agents/skills/tla-to-veil/SKILL.md): translating TLA+
  specifications into Veil, reviewing such translations, and checking them
  against TLC.

## Benchmarking

[scripts/tlc-vs-veil-mc-evaluation.py](scripts/tlc-vs-veil-mc-evaluation.py)
compares TLC and Veil on safety model checking: it runs TLC on 20 TLA+
benchmarks and `#model_check` on their translations, and generates
execution-time and peak-memory comparison plots.

See the [benchmark instructions](Benchmarks/TLA/scripts/README.md#tlc-and-veil-comparison)
for prerequisites and an example command, or run
`python3 scripts/tlc-vs-veil-mc-evaluation.py --help` for options.
