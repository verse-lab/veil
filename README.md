# Veil: A Framework for Automated and Interactive Verification of Transition Systems

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

**Important:** if you use Veil as a library, make sure to also install
[`z3`](https://github.com/Z3Prover/z3), [`cvc5`](https://github.com/cvc5/cvc5),
and [`uv`](https://github.com/astral-sh/uv). See
[`verse-lab/veil-usage-example`](https://github.com/verse-lab/veil-usage-example)
for a fully set-up example project.

## Build

Veil requires [Lean 4](https://github.com/leanprover/lean4),
[`z3`](https://github.com/Z3Prover/z3), [`cvc5`](https://github.com/cvc5/cvc5),
and [`uv`](https://github.com/astral-sh/uv) (the Python project manager). We
have tested Veil on macOS and Ubuntu. Windows with WSL2 is also supported.
Native Windows support is not yet available.

To build Veil run `lake build`. This will build the whole project with
tests in `Tests/` but without case studies. To build the case studies
run `lake build Examples`.

<details close>
<summary><strong>Detailed build instructions</strong></summary>


1. [Install Lean](https://docs.lean-lang.org/lean4/doc/setup.html). We recommend
   installing via [`elan`](https://github.com/leanprover/elan):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable
```

2. Install [`uv`](https://github.com/astral-sh/uv), the Python dependency manager:

```bash
curl -LsSf https://astral.sh/uv/install.sh | sh
```

3. Install `z3` and `cvc5`.
   - For Ubuntu run

     ```bash
     sudo apt update && sudo apt install z3 cvc5
     ```

   - For Mac (using [Homebrew](https://brew.sh/))

     ```bash
     brew install z3 cvc5/homebrew-cvc5/cvc5
     ```

     - Detailed instructions on `cvc5` installation can be found
     [here](https://github.com/cvc5/cvc5/blob/main/INSTALL.rst).
     - If you install `cvc5` by getting the binary make sure to add it
     to your PATH by running:

      For bash:

      ```bash
      echo 'export PATH=$HOME/.local/bin:$PATH' >> ~/.bashrc
      source ~/.bashrc
      ```

      For Zsh:

      ```bash
      echo 'export PATH=$HOME/.local/bin:$PATH' >> ~/.zshrc
      source ~/.zshrc
      ```

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
