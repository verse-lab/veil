# Veil: A Framework for Automated and Interactive Verification of Transition Systems

[![Actions status](https://github.com/verse-lab/veil/actions/workflows/ci.yml/badge.svg)](https://github.com/verse-lab/veil/actions)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)


Veil is a _foundational_ framework for (1) specifying, (2)
implementing, (3) testing, and (4) proving safety (and, in the future,
liveness) properties of state transition systems, with a focus on
distributed protocols.

Veil is embedded in the [Lean 4 proof assistant](https://lean-lang.org/) and provides push-button
verification for transition systems and their properties expressed
decidable fragments of first-order logic, with the full power of a
modern higher-order proof assistant for when automation falls short.

## Veil 2.0 Pre-Release

You are looking at a **pre-release version** of Veil 2.0, the upcoming major
version of Veil. There are still quite a few bugs and rough edges.

If you encounter issues, please [report them to
us](https://github.com/verse-lab/veil/issues/new), so we can fix them before
the release. Your patience and feedback are greatly appreciated!

## Online Playground

We provide a live environment to try out Veil 2.0, at the following URL:

<p align="center"><a href="https://try.veil.dev"><big><b>try.veil.dev</b></big></a></p>

## Build

Veil requires [Lean 4](https://github.com/leanprover/lean4) and
[NodeJS](https://nodejs.org/en/download/). To install those on Linux or MacOS:

```bash
# Install Lean
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable

# Install NodeJS
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.40.3/install.sh | bash
\. "$HOME/.nvm/nvm.sh"
nvm install 24
```

Then, clone Veil:

```bash
git clone https://github.com/verse-lab/veil.git
cd veil && git checkout veil-2.0
```

And, finally, build it:

```bash
lake exe cache get
lake build
```

The `lake exe cache get` command downloads a pre-built version of
[mathlib](https://github.com/leanprover-community/mathlib4), which otherwise
would take a very long time to build.

### Troubleshooting

**(NPM errors)** If you see an error about `npm`, make sure it's in your
`PATH`; the command above installs both `node` and `npm`.

**(cvc5 errors)** If you see an error about `cvc5`, run:

```bash
rm -rf .lake/packages/cvc5
lake build
```

There is a sporadic issue in the build process for
[`lean-cvc5`](https://github.com/abdoo8080/lean-cvc5). Trying to build again
often fixes the problem.
