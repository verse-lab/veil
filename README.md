# State Transition Systems in Lean

We aim to build a _foundational_ framework for (1) specifying, (2) implementing,
(3) testing, and (4) proving safety and liveness properties of state transition
systems, with a focus on distributed protocols.

**Pay-as-you-go.** Recognising that interactive proofs are too labourious for
most projects, we aim to support a _progressive verification_ methodology, where
one can build assurance in the specified (and implemented) system in a gradual
fashion, via testing, model checking, automated verification (of a subset of
desired properties), and finally interactive verification.

**Automated reasoning.** The vision for this project is to become a suitable
substrate for many kinds of automated reasoning tasks related to state
transition systems, including but not limited to:

- invariant and temporal property inference
- model checking
- symbolic verification
- synthesis and repair
- compilation to executable code

**A better TLA+.** We aim to replace TLA+ as the language of choice for
modelling distributed systems. To enable this practically, we ought to be able
to represent all TLA+ specifications within our framework and support both
model-checking (akin to TLC) and proving them (akin to TLAPS).

## Build

The `sauto` tactic relies on a Python wrapper around the Z3 SMT solver
that we have written. Ensure you have Python 3 installed and then either:

```bash
pip3 install z3-solver cvc5 sexpdata
```

or (on Ubuntu)

```bash
apt-get install python3-z3 python3-cvc5 python3-sexpdata
```

### Docker image
We supply a script that creates
a Docker image that can be used for developing and running Veil
projects.
This Docker image is based on x86-64 Linux,
but can be used on ARM computers with any OS
that can run Docker.
To use it with Visual Studio Code, follow these instructions:
1. Make sure Docker is running. Run `./create_docker_image.sh`. 
This will automatically download Veil and install
most of the prerequisites on the created image. This can take up to 10 minutes.
2. Run the container with `docker run -dt --platform=linux/amd64 <image-id>`.
3. On your host computer, install the [Dev Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) VS Code plugin.
4. Connect to the Docker container with the `Dev Containers: Attach to Running Container...` action from the Command Palette
(Ctrl/Cmd + Shift + P).
5. **On the container**, install the [Lean 4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) VS Code plugin. This needs to be done once per container.
6. Initially, Veil will be placed in `/root/veil`. You can move it, or open that folder from
7. Test Veil: Go to any of Veil's example files and run the `Lean 4: Server: Restart File` action from the Command Palette. This may take a while on the first run, as it has to rebuild all of Veil. This, too, should not take
more than 10 minutes.
