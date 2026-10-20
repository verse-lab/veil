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

## Veil 2.0 Pre-Release

You are looking at a pre-release version of Veil 2.0, the upcoming major
version of Veil. There are still a few bugs and rough edges. If you encounter
issues, please [report them to
us](https://github.com/verse-lab/veil/issues/new), so we can fix them before
the release. Your patience and feedback are greatly appreciated!

We provide a live environment to try out Veil 2.0, at the following URL:
<a href="https://try.veil.dev">try.veil.dev</a>

You can ask questions on the [Veil
channel](https://leanprover.zulipchat.com/#narrow/channel/537982-Veil) on the
Lean Zulip, and we will be happy to answer.
 
## Learn Veil

The [Examples/Tutorial](Examples/Tutorial) folder contains extensively commented
walkthrough specifications:

- [Examples/Tutorial/Ring.lean](Examples/Tutorial/Ring.lean) — the Ring Leader
  Election protocol, introducing Veil's syntax and its main commands
  (`#check_invariants`, `#model_check`, `sat`/`unsat trace`).

- [Examples/Tutorial/FloodSet.lean](Examples/Tutorial/FloodSet.lean) — a
  complete walkthrough of Veil's multi-modal workflow via the FloodSet
  synchronous crash-fault agreement protocol: modelling, testing via concrete and
  symbolic model checking, counterexample-driven invariant discovery, and an
  interactive Lean proof

These files are also available in the [online playground](#online-playground), under the Examples button.

An explanation of the constructs of the Veil DSL can be found at
[`docs/DSL-Reference.md`](docs/DSL-Reference.md). 

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

### 2. Install Node.js and Lean

On both Linux and macOS, install [Lean 4](https://github.com/leanprover/lean4)
through [Elan](https://github.com/leanprover/elan) and [Node.js
24](https://nodejs.org/en/download/) (including `npm`) through nvm. Elan will
install the Lean version specified in `lean-toolchain` when you first run
`lake` in the repository:

```bash
set -o pipefail &&
(curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none) &&
. "$HOME/.elan/env" &&
(curl -fsSL https://raw.githubusercontent.com/nvm-sh/nvm/v0.40.7/install.sh | bash) &&
. "$HOME/.nvm/nvm.sh" &&
nvm install 24
```

### 3. Clone and build Veil

Clone Veil, enter the repository, and build it:

```bash
git clone https://github.com/verse-lab/veil.git
cd veil
lake build
```

### Troubleshooting

**(NPM errors)** If you see an error about `npm`, make sure it's in your
`PATH`; the installation command above installs both `node` and `npm`.

**(cvc5 errors)** If you see an error about `cvc5`, run:

```bash
rm -rf .lake/packages/cvc5
lake build
```

There is a sporadic issue in the build process for
[`lean-cvc5`](https://github.com/abdoo8080/lean-cvc5). Trying to build again
often fixes the problem.
