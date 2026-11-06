#!/usr/bin/env python3
"""Check widget availability and cancellation through Lean's real LSP server.

Run after `lake build +Veil`:
  python3 scripts/tests/test-model-check-progress.py

A gated background task keeps the command unfinished until the test releases it.
The widget and term information must remain available while that task is blocked, and
editing the command must cancel its old task. Only a virtual document is edited.
"""

import json
import queue
import time

from lean_lsp import LeanServer, ROOT


SOURCE = '''module
public import Veil

open Lean Elab Command in
@[command_elab Veil.modelCheck, incremental]
public meta def gatedModelCheck : CommandElab := fun stx => do
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
  Veil.elabModelCheck stx

veil module StreamingProgress
individual x : Nat
after_init { x := 0 }
action step { require x < 4; x := x + 1 }
invariant x ≤ 4
#gen_spec
#model_check interpreted {} {} (maxDepth := 3)
end StreamingProgress
'''


def main():
    server = LeanServer('model-check-progress')
    events = server.work / 'events.txt'
    release = server.work / 'release'
    source = SOURCE.replace('EVENTS', json.dumps(str(events))).replace(
        'RELEASE', json.dumps(str(release)))
    uri = (ROOT / 'VeilTest/Regression/StreamingProgress.lean').as_uri()
    line = next(i for i, s in enumerate(source.splitlines()) if s.startswith('#model_check '))
    position = {'line': line, 'character': 2}
    received = []

    def read_events():
        return events.read_text().splitlines() if events.exists() else []

    def request(method, params):
        server.next_id += 1
        request_id = server.next_id
        server.write({'jsonrpc': '2.0', 'id': request_id, 'method': method, 'params': params})
        deadline = time.monotonic() + 20
        while time.monotonic() < deadline:
            msg = server.messages.get(timeout=max(0.01, deadline - time.monotonic()))
            received.append(msg)
            if 'method' in msg and 'id' in msg:
                server.write({'jsonrpc': '2.0', 'id': msg['id'], 'result': None})
            elif msg.get('id') == request_id:
                assert 'error' not in msg, msg
                return msg['result']
        raise AssertionError(f'{method} blocked behind the background task')

    def wait_events(expected):
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            actual = read_events()
            if all(actual.count(event) >= count for event, count in expected.items()):
                return
            time.sleep(0.02)
        raise AssertionError((expected, read_events()))

    try:
        server.initialize()
        server.open(uri, source)
        session = request('$/lean/rpc/connect', {'uri': uri})['sessionId']

        def widgets():
            return request('$/lean/rpc/call', {
                'textDocument': {'uri': uri}, 'position': position, 'sessionId': session,
                'method': 'Lean.Widget.getWidgets', 'params': position,
            })['widgets']

        initial_widgets = widgets()
        assert len(initial_widgets) == 1, initial_widgets
        wait_events({'started': 1})
        assert read_events() == ['started'], read_events()
        term_goal = request('$/lean/plainTermGoal', {
            'textDocument': {'uri': uri},
            'position': {'line': line, 'character': source.splitlines()[line].index('3')},
        })
        assert term_goal and 'Nat' in json.dumps(term_goal), term_goal
        print('Widget and term information available with the background task still blocked.', flush=True)

        server.change(uri, 2, source.replace('maxDepth := 3', 'maxDepth := 4'))
        updated_widgets = widgets()
        assert len(updated_widgets) == 1, updated_widgets
        wait_events({'started': 2, 'cancelled': 1})
        assert 'released' not in read_events(), read_events()
        print('Editing the command cancelled its old task and published a new widget.', flush=True)

        release.touch()
        wait_events({'released': 1})
        server.notifications.extend(received)
        diagnostics = server.diagnostics(uri, 2, 'finished')
        assert not [d for d in diagnostics if d.get('severity') in (1, 2)], diagnostics
        assert sum(d['message'] == 'Gate released' for d in diagnostics) == 1, diagnostics
        assert sum('No violation' in d['message'] for d in diagnostics) == 1, diagnostics
        print('Final diagnostics are complete and are not duplicated.', flush=True)
    except queue.Empty as ex:
        raise AssertionError('LSP request blocked behind the background task') from ex
    finally:
        release.touch()
        (server.work / 'requests.json').write_text(json.dumps(received, indent=2))
        server.close()


if __name__ == '__main__':
    main()
