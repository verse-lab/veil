# Publishing the plugin

## Build a local VSIX

Run the following from the repository root (requires Node.js 22 or later).
The `vsce` tool only needs to be installed once:

```sh
cd editors/vscode
npm install -g @vscode/vsce
npm ci
npm run package:vsix
```

This checks the TypeScript types, builds the production bundles, and writes
`editors/vscode/veil-verifier-<version>.vsix`, using the version in `package.json`.
Local packaging does not require Marketplace credentials. Install the resulting
file with **Extensions: Install from VSIX...** in VS Code, or upload it manually
to the Marketplace.

## Versions

The version of the extension is `0.N.x`, where `N` is the IDE protocol of Veil that it
supports (`IDE_PROTOCOL` in `src/compatibility.ts`), so that users can tell which version fits
their Veil. The patch version counts the releases for one protocol. `vscode:prepublish` refuses
to package another version (`checkVersion.mjs`).

## Publish to Marketplace

Configure publishing credentials for the `verse-lab` publisher using the
[VS Code publishing guide](https://code.visualstudio.com/api/working-with-extensions/publishing-extension#publishing-extensions).

Add the changes of the release to `CHANGELOG.md`, under the next version: the Marketplace shows
it. From `editors/vscode`, build and publish the next patch version:

```sh
npm run publish:marketplace -- patch
```

This checks the version and the TypeScript types, builds the production bundles, increments the
patch version in `package.json` and `package-lock.json`, and uploads the extension. It does not
create a Git commit or tag, so commit the new version afterwards. Without the `patch` argument,
it uploads the version in `package.json`: to retry an upload, or to publish `0.N.0` after a bump
of the IDE protocol (see below). It refuses other version arguments, such as `minor`.

Both commands run `vscode:prepublish` to check the version and the types and to build before
packaging.

## Changing what the extension relies on

`IDE_PROTOCOL` in `src/compatibility.ts` must equal `Veil.ideProtocolVersion` in
`Veil/Core/Tools/ModelChecker/CompiledRuntime.lean`, whose documentation lists what the protocol
covers; `npm test` checks that they are equal. `VeilTest/IDEProtocol.lean` fails when the names
or formats that it shows change.

When a change to Veil would break an extension built before it:

1. In the pull request of the change, bump `ideProtocolVersion` and `IDE_PROTOCOL` together to
   the new protocol `N`, set the version of the extension to `0.N.0` with
   `npm version 0.N.0 --no-git-tag-version`, and update the extension,
   `VeilTest/IDEProtocol.lean`, and `CHANGELOG.md`, saying from which Veil on the version is.
2. Publish the extension right after the change is merged, with `npm run publish:marketplace`
   and no version argument. Until then, projects that update Veil are told to build the
   extension themselves.

An addition that the extension can detect, such as a new code action that it asks for, needs
no bump: the extension goes without it when Lean does not answer.
