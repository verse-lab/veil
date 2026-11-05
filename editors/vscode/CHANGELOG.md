# Changelog

Veil Verifier 0.N.x supports IDE protocol N of Veil: the version of what the extension relies on of
Veil, such as its messages, code actions and model checker binaries (see "Install" in the README).
The versions 0.0.x come from before the extension checked it.

## 0.1.0

IDE protocol 1, for Veil from October 27, 2026 on.

- The extension checks that it supports the Veil of your project. When it does not, the lenses say
  so in place of their actions, and the extension tells you whether to update the extension or
  Veil. **Use Anyway** brings the actions back for the window.
- The panel says when a saved or exported run comes from a binary of another IDE protocol.
- When Lean gives no config template, the warning also says that a Veil older than the extension
  can be the cause.

## 0.0.3

- **Create config from this instantiation**, above a `#model_check` of a module, also in a comment,
  creates a config with the instantiation, the theory and the options of the check.

## 0.0.2

- A run rebuilds the model checker when the model or the config has changed since Lean built it.
- The lens that adds `#gen_executable` also shows above `#gen_spec`.

## 0.0.1

- First version: runs the model checkers that `#mc_config` builds, and shows their progress and
  results in a panel.
