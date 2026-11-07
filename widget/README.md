# Widget development

With Node.js 24 installed, normal `lake build` automatically rebuilds the
JavaScript and Lake trace in `widget/js/` when TypeScript changes. No separate
widget build command is needed.

Commit the updated JavaScript and trace with your TypeScript changes. CI checks
that they match a clean build. After changing npm dependencies, update the lockfile
with `npm install --package-lock-only --prefix widget`.
