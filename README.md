# Veil: A Framework for Automated and Interactive Verification of Transition Systems

[![Actions status](https://github.com/verse-lab/veil/actions/workflows/docker-build-and-test.yml/badge.svg)](https://github.com/verse-lab/veil/actions)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)


Veil is a _foundational_ framework for (1) specifying, (2)
implementing, (3) testing, and (4) proving safety (and, in the future,
liveness) properties of state transition systems, with a focus on
distributed protocols.

Veil is embedded in the [Lean 4 proof assistant](https://lean-lang.org/) and provides push-button
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

## Project Structure

The project consists of three major folders:

- `Veil/`: the implementation of Veil,
- `Test/`: Veil's artificial test cases for main Veil features,
- `Examples/`: Veil's benchmarks, consisting of realistic specifications of distributed protocols

### `Veil/` components

- `DSL/`: Veil DSL
  - `Action/Theory.lean`: meta-theory of action DSL with the soundness proof
  - `Action/Lang.lean`: implementation of action DSL expansion
  - `Specification/Lang.lean`: implementation of protocol declaration commands
- `SMT/`: tactics for interaction with SMT
- `Tactic/`: auxiliary tactics for proof automation

### Case Studies implemented in `Examples/`

- `FO/`: non-EPR protocols
- `IvyBench/`: benchmarks [translated from Ivy](https://github.com/aman-goel/ivybench)
- `Rabia/`: [Rabia protocol](https://github.com/haochenpan/rabia?tab=readme-ov-file)
- `StellarConsensus/`: [Stellar Consensus Protocol](https://github.com/stellar/scp-proofs/tree/3e0428acc78e598a227a866b99fe0b3ad4582914)
- `SuzukiKasami/`: [Suzuki Kasami protocol](https://github.com/markyuen/tlaplus-to-ivy/blob/main/ivy/suzuki_kasami.ivy)

------

### Additional resources

<details close>
<summary><strong>Docker image</strong></summary>

We supply a script that creates a Docker image that can be used for
developing and running Veil projects. This Docker image is based on
x86-64 Linux, but can be used on ARM computers with any OS that can
run Docker. To use it with Visual Studio Code, follow these
instructions:

1. Make sure Docker is running. Run `./create_docker_image.sh`.
This will automatically download Veil and install
most of the prerequisites on the created image. This can take up to 10 minutes.
2. Run the container with `docker run -dt --platform=linux/amd64 <image-id>`.
3. On your host computer, install the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) VS Code plugin.
4. Connect to the Docker container with the `Dev Containers: Attach to Running Container...` action from the Command Palette
(Ctrl/Cmd + Shift + P).
5. **On the container**, install the [Lean 4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) VS Code plugin. This needs to be done once per container.
6. Initially, Veil will be placed in `/root/veil`. You can move it, or open that folder directly from VS Code.
7. Test Veil: Go to any of Veil's example files and run the `Lean 4: Server: Restart File` action from the Command Palette. This may take a while on the first run, as it has to rebuild all of Veil.

</details>
