# Model Checker in VS Code: Architecture

A model checker can be built from a separate Lean config file and then run from
VS Code. This note says which side does what and why, and how the extension is
installed.

## Only Lean

Lean does everything that needs to understand the specification: it checks the
config file, fills in the types left as holes, and reports errors at the right
place.

Lean also does all of the building. The build folders are shared by all Lean
processes and guarded by locks, so that one program cannot break a binary that
another one is building or running. Having VS Code hold these locks while it
runs a binary would be hard, so Lean instead copies each finished binary out of
its build folder, and the extension runs the copy. A Lean option sets how many
copies are kept; the docstring of `#mc_config` has the other details.

## Only the Extension

The extension runs the binaries: it starts a run with the user's settings and
stops it when asked. A run can take a long time and should keep going when a
file is edited, so the extension, not Lean, owns the running process.

The extension also shows progress and results, and keeps past results. It uses
each binary only through its inputs and outputs, and never writes to Lean's
build folders.

## What the Extension Reads from Lean

The extension learns which binary belongs to which config command, and whether
it is ready, from the messages Lean reports for the config file. It reads them
through the public VS Code API, not through the Lean extension's own API, which
is not documented and can change without notice.

A binary reports progress and results in formats defined on the Lean side. The
extension follows these formats instead of defining its own, so it shows the
same data as the Lean infoview, and a format changes on both sides at once.

Templates for new config files follow the same rule: Lean provides the content,
because only Lean knows what a module needs, and the extension only places it
in the editor.

## When the Model Changes

When Lean opens a config, it loads the compiled versions of the modules that
the config imports, such as the model. Lean keeps using these versions until
the config is restarted. So the config does not see a change to the model,
even once the model is saved.

Before each run, including **Check again**, the extension saves the Lean files
with unsaved changes. It then invokes **Restart File** on the config if another
Lean file has changed since Lean loaded these versions, or if Lean reports them
as out of date. It also does so after a failed build, or when the binary is gone.
Lean then rebuilds only what changed. Otherwise, the extension runs the binary
that Lean has built, once Lean has finished building it.

After a restart, the extension waits until Lean drops the old result and
reports a new one. A Lean file saved meanwhile stops the run, since the rebuild
may not include it.

Once a direct import of a config is saved, such as the model, Lean reports that
the imports of the config are out of date. The **Last result** lens and the
panel then mark the result as outdated.

## Installing the Extension

Install **Veil Verifier** (`verse-lab.veil-verifier`) from the VS Code Marketplace:

```sh
code --install-extension verse-lab.veil-verifier
```

The extension and the project's Veil revision must use compatible configuration
templates, build messages, and result formats. For local development, use the
Extension Development Host or install a VSIX built from the matching Veil checkout
with **Extensions: Install from VSIX...**.

See the [extension README](../editors/vscode/README.md#develop) for development
instructions and the [publishing guide](../editors/vscode/PUBLISHING.md) for VSIX
packaging and Marketplace publishing.
