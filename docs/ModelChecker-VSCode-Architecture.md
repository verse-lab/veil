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
copies are kept; the docstring of `#model_check_build` has the other details.

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

## Installing the Extension

The extension is installed for each workspace separately, from the copy of Veil
that the workspace uses. Since it follows formats defined by Veil, it has to
come from the same version of Veil. A single install for all of VS Code cannot
do this when workspaces use different versions, for example several clones of
Veil on one machine.

VS Code (1.89 or later) supports this with local workspace extensions. To
install the extension, run this in the workspace:

```sh
lake script run veilInstallVSCodeExtension
```

The script builds the extension with npm and copies it to
`.vscode/extensions/veil-model-checker`. Then reload the VS Code window: VS Code
offers to install the recommended extensions of the workspace, and you choose
Install. If it does not offer, install the extension from Workspace
Recommendations in the Extensions view. This needs the workspace to be trusted,
and is needed only once per workspace: after updating Veil, run the script again
and reload the window. The copy is build output, so keep it out of version
control. The docstring of the script in `lakefile.lean` has the other details.
