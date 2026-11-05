"""Shared parts of the LSP regressions for incremental proof commands.

The regressions instrument proofs with tactics that append a marker to an
execution log, edit a virtual document, and compare the markers logged since the
edit, so replayed diagnostics cannot be mistaken for proof reuse.
"""
import argparse
from collections import Counter
import json
import textwrap
import time

from lean_lsp import ROOT, LeanServer


def replace_once(source, old, new):
    assert source.count(old) == 1, f'expected exactly one {old!r}'
    return source.replace(old, new)


def defer(source, module):
    """Turn on `veil.deferVCGeneration` from `veil module <module>` to the end of `source`."""
    header = f'veil module {module}\n'
    return replace_once(source, header, 'set_option veil.deferVCGeneration true\n' + header)


class ProofDocument:
    """A virtual document whose proofs log their tactic executions."""

    def __init__(self, server, path):
        self.server = server
        self.path = ROOT / path
        self.uri = self.path.as_uri()
        self.log = server.work / 'executions.txt'
        self.log.write_text('')
        self.release = server.work / 'release'
        self.source = None
        self.version = 0

    def logged(self, template):
        """`template` with `LOG` replaced by the execution log, as a Lean string."""
        return template.replace('LOG', json.dumps(str(self.log)))

    def counted(self, marker):
        """A proof line that logs `marker`."""
        return self.logged(f'  run_tac IO.FS.withFile LOG .append fun h => h.putStrLn "{marker}"\n')

    def gate(self, name, body='pure ()', indent='  '):
        """`do` items that log `<name>-start`, run `body` once `release` exists, and
        log `<name>-finish`, or `<name>-cancelled` when interrupted: `catch` does not
        see interrupts, but `finally` runs on them."""
        return textwrap.indent(self.logged(f'''\
IO.FS.withFile LOG .append fun h => h.putStrLn "{name}-start"
let finished ← IO.mkRef false
try
  while !(← System.FilePath.pathExists {json.dumps(str(self.release))}) do
    Lean.Core.checkInterrupted
    IO.sleep 10
  Lean.Core.checkInterrupted
  {body}
  finished.set true
finally
  let marker := if (← finished.get) then "{name}-finish" else "{name}-cancelled"
  IO.FS.withFile LOG .append fun h => h.putStrLn marker
'''), indent)

    def observer(self, kind, elaborator):
        """A command elaborator for `kind` that delegates to `elaborator`, and logs
        `theorem-snapshot` once the generated theorem resolves the command's snapshot."""
        return self.logged(f'''\
open Lean Elab Command in
@[command_elab {kind}, incremental]
public meta def observeProofCommand : CommandElab := fun stx => do
  if let some snap := (← read).snap? then
    let _ ← IO.asTask (prio := .dedicated) do
      if (← IO.wait snap.new.result?).isSome then
        IO.FS.withFile LOG .append fun h => h.putStrLn "theorem-snapshot"
    pure ()
  {elaborator} stx
''')

    def executions(self):
        return self.log.read_text().splitlines()

    def wait_for(self, marker, count=1, since=0):
        """Wait until `marker` is logged `count` times after the first `since` executions."""
        deadline = time.monotonic() + 30
        while time.monotonic() < deadline:
            if self.executions()[since:].count(marker) >= count:
                return
            time.sleep(0.01)
        raise AssertionError(f'timed out waiting for {marker}: {self.executions()}')

    def goal(self, line, character):
        goal = self.server.send('$/lean/plainGoal', {'textDocument': {'uri': self.uri},
                                'position': {'line': line, 'character': character}}, True)
        print('goal:', goal, flush=True)
        assert goal, (line, character)
        return goal['rendered']

    def send(self, source):
        """Send `source` as the next version, without waiting for its elaboration."""
        self.source = source
        self.version += 1
        if self.version == 1:
            self.server.open(self.uri, source)
        else:
            self.server.change(self.uri, self.version, source)

    def change(self, source, label, check=None):
        """Send `source` and return the markers logged until its diagnostics are ready.
        `check` inspects the diagnostics; by default, there must be no errors or warnings."""
        before = len(self.executions())
        self.send(source)
        if check is None:
            self.server.check(self.uri, self.version, label)
        else:
            check(self.server.diagnostics(self.uri, self.version, label))
        executions = self.executions()[before:]
        print(label, 'new executions:', executions, flush=True)
        return executions

    def edit(self, label, *replacements):
        """`change` to the current source with each `(old, new)` in `replacements` applied."""
        source = self.source
        for old, new in replacements:
            source = replace_once(source, old, new)
        return self.change(source, label)


def check_multi_module_reuse(doc, source, last_tactic, check_goals, start):
    """Edit in turn the proofs of two modules, `first` and `second`, each ending with
    the line `<last_tactic> -- <which> proof`. Proof `which` logs `start[which]` when
    it starts; a `prefix:<which>` tactic is inserted before its last tactic.
    `check_goals` runs after every edit."""
    for which in ('first', 'second'):
        last = f'  {last_tactic} -- {which} proof\n'
        source = replace_once(source, last, doc.counted(f'prefix:{which}') + last)
    assert Counter(doc.change(source, 'fresh two-module proofs')) == Counter({
        start['first']: 1, 'prefix:first': 1, start['second']: 1, 'prefix:second': 1,
    }), doc.executions()
    check_goals()

    def edit(old, new, label):
        delta = Counter(doc.edit(label, (old, new)))
        check_goals()
        return delta

    first = f'  {last_tactic} -- first proof'
    second = f'  {last_tactic} -- second proof'
    delta = edit(second, '  skip\n' + second, 'edit second proof suffix')
    assert not delta, delta
    delta = edit('"prefix:second"', '"prefix:second2"', 'edit second proof prefix')
    assert delta == Counter({'prefix:second2': 1}), delta
    delta = edit(first, '  skip\n' + first, 'edit first proof after second module')
    # Later commands may legitimately re-elaborate when an earlier proof changes.
    # The first proof must reuse its own unchanged start and prefix.
    assert delta[start['first']] == 0 and delta['prefix:first'] == 0, delta
    delta = edit('  skip\n' + second, second, 'edit second proof after first-module edit')
    assert not delta, delta
    delta = edit('"prefix:first"', '"prefix:first2"', 'edit first proof prefix')
    assert delta[start['first']] == 0 and delta['prefix:first2'] == 1, delta
    delta = edit(second, '  skip\n' + second, 'reuse second proof after first prefix change')
    assert not delta, delta


def check_edit_while_running(doc, source, name, later_edit):
    """Send `source`, in which `doc.gate(name)` holds a step of the proof and
    `doc.observer` wraps the proof command, then apply `later_edit` to a later tactic
    while the step waits. The step must run once, to completion: the edited proof
    reuses it rather than cancelling it. The gate opens once the observer reports the
    edited theorem, so this does not depend on guessing how long deferred preparation
    or scheduling takes. Returns the markers logged meanwhile."""
    before = len(doc.executions())
    doc.send(source)
    doc.wait_for(f'{name}-start', since=before)
    doc.wait_for('theorem-snapshot', since=before)
    assert f'{name}-finish' not in doc.executions()[before:]
    doc.send(replace_once(source, *later_edit))
    doc.wait_for('theorem-snapshot', count=2, since=before)
    doc.release.write_text('continue')
    label = f'edit while {name} is running'
    doc.server.check(doc.uri, doc.version, label)
    executions = doc.executions()[before:]
    print(label, 'new executions:', executions, flush=True)
    assert executions.count(f'{name}-start') == 1, executions
    assert executions.count(f'{name}-finish') == 1, executions
    assert f'{name}-cancelled' not in executions, executions
    return executions


def main(description, name, run_single_module, run_multi_module):
    """Run `run_single_module`, or `run_multi_module` with `--multi-module`, on a fresh
    Lean server. Both take the server and whether `--deferred` was passed."""
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument('--deferred', action='store_true', help='defer VC generation until the proof command')
    parser.add_argument('--multi-module', action='store_true', help='check tactic reuse across two Veil modules')
    args = parser.parse_args()
    server = LeanServer(name + ('-multi' if args.multi_module else '') + ('-deferred' if args.deferred else ''))
    try:
        server.initialize()
        (run_multi_module if args.multi_module else run_single_module)(server, args.deferred)
        print('PASS; evidence:', server.work, flush=True)
    finally:
        server.close()
