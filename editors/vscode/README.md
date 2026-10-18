# Veil Model Checker for VS Code

Runs the model checkers that `#model_check_build` builds, and shows their progress
and results. See [ModelChecker-VSCode-Architecture.md](../../docs/ModelChecker-VSCode-Architecture.md)
for what the extension does and what Lean does.

## Use

Write a config file that imports a module with `#gen_executable`, and build a model
checker for it:

```lean
module
public import Veil
public import MyProject.Paxos

#model_check_build Paxos { acceptor := Fin 3, value := Fin 2, MsgSet := OrdList _ } {}
```

Once Lean has built the binary, a **Run model checker** lens appears above the
command. The run shows in the **Veil Model Checking** panel and in the status bar,
and **Stop** ends it. The command palette has the same commands under "Veil".

The extension keeps the last result of each command, also after VS Code restarts,
and a **Last result** lens above the command shows it. **Export...** in the panel
saves a result to a file, and **Veil: Open Model Checking Result...** shows such a
file, or a result that a binary printed on the command line.

The settings `veil.modelChecker.workers` (`0` for all cores, `1` for the sequential
checker), `veil.modelChecker.thresholdToParallel` and `veil.modelChecker.numSubSteps`
set how a run is parallelized.

## Develop

```sh
cd editors/vscode
npm install
npm run build   # or: npm run watch
npm test        # needs a built Veil: it builds the binaries of test/fixtures with lake
```

To try the extension, open `editors/vscode` in VS Code and run **Run Extension**
(F5). This opens the repository in a new window with the extension loaded.
