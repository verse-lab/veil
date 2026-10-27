# Publishing the plugin

Install the `vsce` publishing tool once (requires Node.js 22 or later), then
install the extension's dependencies from `editors/vscode`:

```sh
npm install -g @vscode/vsce
npm ci
```

Configure publishing credentials for the `verse-lab` publisher using the
[VS Code publishing guide](https://code.visualstudio.com/api/working-with-extensions/publishing-extension#publishing-extensions).

To build and publish the next patch version:

```sh
npm run publish:marketplace -- patch
```

This checks the TypeScript types, builds the production bundles, increments the
patch version in `package.json` and `package-lock.json`, and uploads the extension.
It does not create a Git commit or tag. Use `minor` or `major` instead of `patch`
for a larger version change. To retry an upload using the current version, omit
the version argument.

To build a VSIX for local testing or manual upload without publishing:

```sh
npm run package:vsix
```

Both commands run `vscode:prepublish` to check types and build before packaging.
