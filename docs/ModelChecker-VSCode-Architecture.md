# Model Checker in VS Code: Architecture

A model checker can be built from a separate Lean config file and then run from
VS Code. This note says which side does what, and why.

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
