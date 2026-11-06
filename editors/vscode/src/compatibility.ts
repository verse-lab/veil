// Whether this extension supports the IDE protocol that the Veil of a project reports. This module
// is shared with the webview, so it must not import Node or VS Code modules.

/** The IDE protocol that this extension supports: `Veil.ideProtocolVersion` of its Veil, and the
 * minor version of the extension (see PUBLISHING.md) */
export const IDE_PROTOCOL = 1;

/** The IDE protocol of a Veil from before it reported one, which answers
 * `refactor.veil.executableModules` (October 27, 2026 on). Older Veils answer neither, as Lean does
 * before it has processed a file, so they count as unknown. */
export const LEGACY_IDE_PROTOCOL = 1;

export type Incompatibility = { kind: 'olderVeil' | 'newerVeil'; protocol: number };

export type Compatibility =
  /** Lean has not said, e.g. because it has not processed the imports of the file yet */
  | { kind: 'unknown' }
  | { kind: 'supported' }
  | Incompatibility;

/** Whether this extension supports a Veil that reports `protocol`; `undefined` if Lean has not said */
export function compatibility(protocol: number | undefined): Compatibility {
  if (protocol === undefined) return { kind: 'unknown' };
  if (protocol === IDE_PROTOCOL) return { kind: 'supported' };
  return { kind: protocol < IDE_PROTOCOL ? 'olderVeil' : 'newerVeil', protocol };
}

export function isIncompatible(found: Compatibility): found is Incompatibility {
  return found.kind === 'olderVeil' || found.kind === 'newerVeil';
}

/** What to tell the user about a Veil that this extension, of `extensionVersion`, does not support */
export function incompatibilityMessage(veil: Incompatibility, extensionVersion: string): string {
  const versions = `it reports IDE protocol ${veil.protocol}, and Veil Verifier ${extensionVersion} ` +
    `supports IDE protocol ${IDE_PROTOCOL}.`;
  // The extension of each IDE protocol N has the versions 0.N.x
  const line = `0.${veil.protocol}.x`;
  if (veil.kind === 'newerVeil') {
    return `The Veil of this project is newer than this extension supports: ${versions} Update the extension ` +
      `to a version ${line}. If none is available yet, build it from the copy of Veil that the project uses: ` +
      'see "Build a local VSIX" in .lake/packages/veil/editors/vscode/PUBLISHING.md.';
  }
  return `The Veil of this project is older than this extension supports: ${versions} Update Veil in the ` +
    `project with "lake update veil", or install the latest version ${line} of the extension with "Install ` +
    'Specific Version..." in the Extensions view, and turn off its auto update.';
}

/** What a command adds when Lean gives it nothing, while Lean has not said which IDE protocol the
 * Veil of the file uses */
export const UNKNOWN_VEIL_HINT = 'Lean also gives none if the Veil of this project is older than this ' +
  'extension supports, e.g. from before October 27, 2026: then update it with "lake update veil".';

/** What the panel says of a run whose binary reported `protocol`, if it is not the one of this
 * extension */
export function otherProtocolNotice(protocol: number | undefined): string | undefined {
  if (protocol === undefined || protocol === IDE_PROTOCOL) return undefined;
  return `The binary of this run reported IDE protocol ${protocol}, and this extension supports IDE ` +
    `protocol ${IDE_PROTOCOL}: the panel may not show the run correctly.`;
}
