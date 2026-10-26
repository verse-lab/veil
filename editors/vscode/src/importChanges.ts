// Whether the imports of an open Lean file may have changed since Lean read them. This module does
// not use VS Code, so that the tests can run it.

/** Lean reads the imports of a file when it opens or restarts the file, and keeps them until it
 * restarts the file again. On opening, Lean reports imports that need rebuilding, so only later
 * changes are tracked here. The imports of a file are not known here, so a change to any other Lean
 * file counts. */
export class ImportChanges {
  /** Orders the changes and the reads */
  private clock = 0;
  private readonly changedAt = new Map<string, number>();
  private readonly readAt = new Map<string, { at: number; version?: number }>();

  /** `file` was saved, or changed on disk */
  changed(file: string): void {
    this.changedAt.set(file, ++this.clock);
  }

  /** The point of the changes so far, for `read` */
  now(): number {
    return this.clock;
  }

  /** Lean has read the imports of `file` as they were `at`, e.g. when it was asked to restart the
   * file, or reads them now, as it opens the file */
  read(file: string, at = this.clock, version?: number): void {
    this.readAt.set(file, { at, version });
  }

  /** Whether the file has been edited since the version whose imports Lean read */
  hasBeenEdited(file: string, version: number): boolean {
    return this.readAt.get(file)?.version !== version;
  }

  /** `file` was closed, so Lean will read its imports again when it opens the file */
  closed(file: string): void {
    this.readAt.delete(file);
  }

  /** Whether another file may have changed since Lean read the imports of `file` */
  mayHaveChanged(file: string): boolean {
    const read = this.readAt.get(file);
    if (read === undefined) return true;
    for (const [other, at] of this.changedAt) if (other !== file && at > read.at) return true;
    return false;
  }
}
