# Veil for VS Code

Runs the model checkers that `#model_check_build` builds, and shows their progress
and results. See [ModelChecker-VSCode-Architecture.md](../../docs/ModelChecker-VSCode-Architecture.md)
for what the extension does and what Lean does.

## Install

Run `lake script run veilInstallVSCodeExtension` in a workspace that uses Veil,
reload the window, and choose Install when VS Code offers the recommended
extensions. See [Installing the Extension](../../docs/ModelChecker-VSCode-Architecture.md#installing-the-extension).

## Use

Write a config file that imports a module with `#gen_executable`, and build a model
checker for it:

```lean
module
public import Veil
public import MyProject.Paxos

#model_check_build Paxos { acceptor := Fin 3, value := Fin 2, MsgSet := OrdList _ } {}
```

**Check model**, above each `veil module` and its `#gen_executable`, runs a config
file of the module once Lean has built it, or else creates `<File>MC.lean` next to the
module, with the values to fill in. Lean gives the template, whose values are holes
(`_`): Lean fills in those that the module's constraints determine, such as `MsgSet`
above, and reports the others for you to fill in.

Once Lean has built the binary, a **Run model checker** lens appears above the
command. The run shows in the **Veil Model Checking** panel and in the status bar,
and **Stop** ends it. The command palette has the same commands under "Veil".

The extension keeps the last result of each command, also after VS Code restarts,
and a **Last result** lens above the command shows it. **Export...** in the panel
saves a result to a file, and **Veil: Open Model Checking Result...** shows such a
file, or a result that a binary printed on the command line.

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

```sh
cd editors/vscode
npm install
npm run build   # or: npm run watch
npm test        # needs a built Veil: it builds the binaries of test/fixtures with lake
```

To try the extension, open `editors/vscode` in VS Code and run **Run Extension**
(F5). This opens the repository in a new window with the extension loaded.
