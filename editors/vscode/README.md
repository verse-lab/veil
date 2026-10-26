# Veil for VS Code

Run model checkers for [Veil](https://github.com/verse-lab/veil) specifications
from VS Code. Track progress, inspect counterexamples, and save or export results.
Lean builds the model checkers through `#mc_config`; the extension runs the
generated executables and displays their progress and results.

## Install

In the Extensions view, search for `@id:verse-lab.veil-verifier` and choose **Install**,
or run:

```sh
code --install-extension verse-lab.veil-verifier
```

Open the root folder of a Lean project that uses Veil. Model checking requires
the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
and a working Veil build, using the Lean toolchain specified by your project.
See the [Veil setup instructions](https://github.com/verse-lab/veil#build)
for the required tools and build steps.

This extension uses Veil's `#gen_executable` and `#mc_config` workflow and follows
Veil's build messages and result format. If your project uses an incompatible
Veil revision, build the extension from that revision as described under
[Develop](#develop).

## Use

Open a Lean file containing a `veil module`. The clickable actions above the
module and its `#gen_executable` guide you through creating a config and running
the model checker.

A config file imports your module and supplies its finite types and theory
values. For example, for a `Paxos` module defined in `MyProject/Paxos.lean`:

```lean
module
public import Veil
public import MyProject.Paxos

#mc_config Paxos { acceptor := Fin 3, value := Fin 2, MsgSet := OrdList _ } {}
```

Replace the import, module name, and parameters with those of your specification.

The lens above each `veil module` and its `#gen_executable` names the next action:
**Add #gen_executable** inserts the missing command; **Create model checking config**
creates and opens `<File>MC.lean` next to the module, with values to fill in. Once a
config exists, **Run model checker** opens it and runs once Lean has built it. With
several configs, **Select config and run...** lets you choose which one to run.
Lean gives the template, whose values are holes (`_`): Lean fills in those that the
module's constraints determine, such as `MsgSet` above, and reports the others for
you to fill in.

The lens above the command runs its model checker. It reads **Run model checker**
once Lean has built the binary, and **Run once built** while Lean is building it.
It reads **Rebuild and run model checker** when the build failed, or when a file
that the config imports, such as the model, was saved since Lean built it. A run
first saves your Lean changes, and Lean then rebuilds what they affect. The run
shows in the **Veil Model Checking** panel and in the status bar, and **Stop**
ends it. The command palette has the same commands under "Veil".

The extension keeps the last result of each command, also after VS Code restarts,
and a **Last result** lens above the command shows it. The lens marks the result
as outdated once the model or the config has changed since the run. **Export...**
in the panel saves a result to a file, and **Veil: Open Model Checking Result...**
shows such a file, or a result that a binary printed on the command line.

## Settings

`veil.modelChecker.maxSavedResults` limits the saved results per workspace
(default `50`, minimum `1`). Each command keeps only its latest result. When the
limit is exceeded, the oldest results are removed. Changes to the limit take
effect the next time a result is saved.

The settings `veil.modelChecker.workers` (`0` for all cores, `1` for the sequential
checker), `veil.modelChecker.thresholdToParallel` and `veil.modelChecker.numSubSteps`
set how a run is parallelized. **Run with options...** sets it for one run instead,
which **Check again** repeats. A config file cannot set it: the binary takes it as
arguments.

## Develop

From a Veil checkout:

```sh
cd editors/vscode
npm ci
npm run typecheck
npm run build   # or: npm run watch
npm test        # needs a built Veil: it builds the binaries of test/fixtures with lake
```

To try the extension, open `editors/vscode` in VS Code and run **Run Extension**
(F5). This opens the repository in a new window with the extension loaded.

To install the extension from the Veil revision used by a workspace, run this
from the workspace root (requires Node.js and npm):

```sh
lake script run veilInstallVSCodeExtension
```

Reload the window with **Developer: Reload Window** and install Veil from
**Workspace Recommendations** in the Extensions view. Local workspace extensions
require VS Code 1.89 or later and a trusted workspace. After updating Veil, run
the script again and reload the window.

## Feedback

Report bugs and feature requests in the
[Veil issue tracker](https://github.com/verse-lab/veil/issues).
