#!/usr/bin/env python3
"""Check, through Lean's real LSP server, that the commands with a streaming widget publish it while
their work still runs (see `Veil.withStreamingInfo`).

Run after `lake build +Veil`, for all commands or the named ones:
  python3 scripts/tests/test-streaming-widgets.py [model_check simulate ...]

In each case, an elaborator in front of the command's own logs a background task that blocks until
the test releases it, so that the command's final info tree is incomplete until then. While the task
is blocked, Lean must answer what the infoview asks at the cursor, inside the command and at the end
of its line, including the widget and the term information of the command, and say its IDE protocol
at the end of the imports, where the VS Code extension asks. Editing the command must cancel its old
task, and the final diagnostics must be complete and not duplicated. Only virtual documents are
edited.
"""

import json
import sys
import time
from dataclasses import dataclass
from typing import Optional

from lean_lsp import LeanServer, ROOT


# The warning of the commands that check with an SMT solver, which they give once
TRUSTED_SOLVER = 'Trusting SMT solver for'

HEADER = '''module
public import Veil

public meta section
open Lean Elab Command

/-- A background task of the command, which blocks until the test releases it -/
def gate : CommandElabM Unit := do
  let token ← IO.CancelToken.new
  let act ← wrapAsyncAsSnapshot (fun () => do
    IO.FS.withFile EVENTS .append fun h => h.putStrLn "started"
    while !(← token.isSet) && !(← System.FilePath.pathExists RELEASE) do
      IO.sleep 20
    if ← token.isSet then
      IO.FS.withFile EVENTS .append fun h => h.putStrLn "cancelled"
    else
      IO.FS.withFile EVENTS .append fun h => h.putStrLn "released"
      logInfo "Gate released") token
  let task ← BaseIO.asTask (act ()) (prio := .dedicated)
  logSnapshotTask { stx? := none, cancelTk? := token, task }

'''


def gated(kind, elaborator):
    """The command's elaborator, behind the gate"""
    return f'''@[command_elab {kind}, incremental]
def gated : CommandElab := fun stx => do
  gate
  {elaborator} stx

end
'''


COUNTER = '''
veil module StreamingCounter
individual x : Nat
after_init {{ x := 0 }}
action step {{ require x < 4; x := x + 1 }}
{extra}invariant x ≤ 4
#gen_spec
{command}
end StreamingCounter
'''

FLAG = '''
veil module StreamingFlag
individual flag : Bool
after_init { flag := false }
action flip { flag := !flag }
invariant [boolean] flag = true ∨ flag = false
#gen_spec
COMMAND
end StreamingFlag
'''

TOKEN_PASSING = '''
veil module TokenPassing
type node
relation tok : node → Bool
individual stopped : Bool
#gen_state
after_init {
  tok N := true
  stopped := false
}
action pass (n m : node) {
  require tok n
  tok n := false
  tok m := true
}
action finish {
  require ∀ N, ¬ tok N
  stopped := true
}
safety [never_stopped] ¬ stopped
#gen_spec
COMMAND
end TokenPassing
'''


@dataclass
class Case:
    """A command whose work runs in the background while its widget shows its progress"""
    gate: str
    body: str
    command: str
    # A unique part of the final message that reports the result of the command
    result: str
    # A numeral in the command, whose type the term information must give
    numeral: Optional[str] = None
    edit: Optional[str] = None

    def edited(self, source):
        """`source` with the command changed, so that Lean elaborates it again"""
        new = self.command.replace(*self.edit.split(' -> ')) if self.edit else self.command + ' -- edited'
        assert new != self.command
        return source.replace(self.command, new)


CASES = {
    'model_check': Case(
        gated('Veil.modelCheck', 'Veil.elabModelCheck'),
        COUNTER.format(extra='', command='{command}'),
        '#model_check interpreted {} {} (maxDepth := 3)', 'No violation',
        numeral='3', edit='maxDepth := 3 -> maxDepth := 4'),
    'simulate': Case(
        gated('Veil.simulate', 'Veil.elabSimulate'),
        COUNTER.format(extra='', command='{command}'),
        '#simulate interpreted {} {} (seed := 1) (numTraces := 2) (maxSteps := 3)', 'No violation in 2 traces',
        numeral='3', edit='maxSteps := 3 -> maxSteps := 2'),
    'temporal_check': Case(
        gated('Veil.livenessCheck', 'Veil.elabLivenessCheck'),
        COUNTER.format(extra='temporal (only := check) [bounded] □ ⌜ x ≤ 4 ⌝\n', command='{command}'),
        '#temporal_check interpreted {} {}', 'No liveness violation'),
    'check_invariants': Case(
        gated('Veil.checkInvariants', 'Veil.elabCheckInvariants'),
        FLAG.replace('COMMAND', '{command}'),
        '#check_invariants', 'must preserve the invariant'),
    'check_action': Case(
        gated('Veil.checkAction', 'Veil.elabCheckAction'),
        FLAG.replace('COMMAND', '{command}'),
        '#check_action flip', 'must preserve the invariant'),
    # The trace commands have no named syntax kind: gate them by their syntax instead
    'trace': Case(
        '''@[incremental] elab_rules : command
  | `(command| $r:expected_smt_result trace [ $name ] { $spec:traceSpec }) => do
    gate
    Veil.elabTraceSpec r (some name) spec none

end
''',
        FLAG.replace('COMMAND', '{command}'),
        'sat trace [flipped] { flip }', 'Satisfying trace found'),
    'updr': Case(
        gated('Veil.Synthesizer.updr', 'Veil.Synthesizer.elabUpdr'),
        TOKEN_PASSING.replace('COMMAND', '{command}'),
        '#updr (expect := no_universal_invariant)', 'No universal inductive invariant'),
}


def run_case(name, case):
    server = LeanServer(f'streaming-{name}')
    events = server.work / 'events.txt'
    release = server.work / 'release'
    source = (HEADER + case.gate + case.body.replace('{command}', case.command)).replace(
        'EVENTS', json.dumps(str(events))).replace('RELEASE', json.dumps(str(release)))
    uri = (ROOT / f'VeilTest/Regression/StreamingWidget_{name}.lean').as_uri()
    lines = source.splitlines()
    line = lines.index(case.command)
    imports_line = lines.index('public import Veil')
    received = []

    def read_events():
        return events.read_text().splitlines() if events.exists() else []

    def request(method, params, timeout=60):
        server.next_id += 1
        request_id = server.next_id
        server.write({'jsonrpc': '2.0', 'id': request_id, 'method': method, 'params': params})
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            try:
                msg = server.messages.get(timeout=max(0.01, deadline - time.monotonic()))
            except Exception:
                break
            received.append(msg)
            if 'method' in msg and 'id' in msg:
                server.write({'jsonrpc': '2.0', 'id': msg['id'], 'result': None})
            elif msg.get('id') == request_id:
                assert 'error' not in msg, msg
                return msg['result']
        raise AssertionError(f'{name}: {method} blocked behind the background task')

    def wait_events(expected, timeout=30):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            actual = read_events()
            if all(actual.count(event) >= count for event, count in expected.items()):
                return
            time.sleep(0.02)
        raise AssertionError((name, expected, read_events()))

    try:
        server.initialize()
        server.open(uri, source)
        session = request('$/lean/rpc/connect', {'uri': uri})['sessionId']

        def infoview_requests(command):
            """What the infoview asks at the cursor, which shows the widget once all of it is answered:
            inside the command, and at the end of its line, where the cursor is after typing it"""
            for character in (2, len(command)):
                at = {'line': line, 'character': character}
                tdpp = {'textDocument': {'uri': uri}, 'position': at}

                def rpc(method, params):
                    return request('$/lean/rpc/call', {**tdpp, 'sessionId': session, 'method': method, 'params': params})
                rpc('Lean.Widget.getInteractiveGoals', tdpp)
                rpc('Lean.Widget.getInteractiveTermGoal', tdpp)
                widgets = rpc('Lean.Widget.getWidgets', at)['widgets']
                assert len(widgets) == 1, (name, at, widgets)
                rpc('Lean.Widget.getInteractiveDiagnostics', {'lineRange': {'start': line, 'end': line + 1}})

        # The gate starts once Lean has elaborated the commands before this one
        wait_events({'started': 1}, timeout=300)
        infoview_requests(case.command)
        assert read_events() == ['started'], (name, read_events())
        if case.numeral:
            term_goal = request('$/lean/plainTermGoal', {
                'textDocument': {'uri': uri},
                'position': {'line': line, 'character': case.command.index(case.numeral)},
            })
            assert term_goal and 'Nat' in json.dumps(term_goal), (name, term_goal)
        end_of_imports = {'line': imports_line, 'character': len(lines[imports_line])}
        actions = request('textDocument/codeAction', {
            'textDocument': {'uri': uri}, 'range': {'start': end_of_imports, 'end': end_of_imports},
            'context': {'diagnostics': [], 'only': ['refactor.veil.ideProtocol']},
        })
        assert [a for a in actions if a.get('command', {}).get('command') == 'veil.ideProtocol'], (name, actions)
        term = ', with the term information,' if case.numeral else ''
        print(f'{name}: the requests of the infoview{term} and the IDE protocol are answered with the '
              'background task still blocked.', flush=True)

        edited = case.edited(source)
        server.change(uri, 2, edited)
        infoview_requests(edited.splitlines()[line])
        wait_events({'started': 2, 'cancelled': 1})
        assert 'released' not in read_events(), (name, read_events())
        print(f'{name}: editing the command cancelled its old task and published a new widget.', flush=True)

        release.touch()
        wait_events({'released': 1})
        server.notifications.extend(received)
        diagnostics = server.diagnostics(uri, 2, f'{name}: finished')
        problems = [d for d in diagnostics if d.get('severity') == 1
                    or d.get('severity') == 2 and not d['message'].startswith(TRUSTED_SOLVER)]
        assert not problems, (name, diagnostics)
        reported = [(d['message'], json.dumps(d['range'], sort_keys=True)) for d in diagnostics]
        assert len(reported) == len(set(reported)), (name, 'duplicated diagnostics', diagnostics)
        assert sum(d['message'] == 'Gate released' for d in diagnostics) == 1, (name, diagnostics)
        assert sum(case.result in d['message'] for d in diagnostics) == 1, (name, diagnostics)
        print(f'{name}: the final diagnostics are complete and are not duplicated.', flush=True)
    finally:
        release.touch()
        (server.work / 'requests.json').write_text(json.dumps(received, indent=2))
        server.close()


def main():
    names = sys.argv[1:] or list(CASES)
    unknown = [n for n in names if n not in CASES]
    assert not unknown, f'unknown cases {unknown}; known: {list(CASES)}'
    for name in names:
        run_case(name, CASES[name])
    print(f'PASS: {", ".join(names)}', flush=True)


if __name__ == '__main__':
    main()
