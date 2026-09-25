#!/usr/bin/env python3
"""Exercise verifier sessions through Lean's actual incremental editor protocol.

Run after `lake build VeilTest`: python3 scripts/test-verifier-lsp.py
"""
import json
import os
import queue
import subprocess
import tempfile
import threading
import time
from pathlib import Path
root = Path(__file__).resolve().parents[1]
uri = (root / '.lake' / 'ManagerLspSmoke.lean').as_uri()
source = (root / 'VeilTest/TwoModulesSameFile.lean').read_text()
messages = queue.Queue()
stderr = tempfile.TemporaryFile(mode='w+')
proc = subprocess.Popen(['lake', 'env', 'lean', '--server'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=stderr, cwd=root)
def read():
    try:
        while True:
            headers = {}
            while True:
                line = proc.stdout.readline()
                if not line:
                    raise EOFError('server exited')
                if line == b'\r\n':
                    break
                k, v = line.decode().split(':', 1)
                headers[k.lower()] = v.strip()
            messages.put(json.loads(proc.stdout.read(int(headers['content-length']))))
    except Exception as ex:
        messages.put(ex)
threading.Thread(target=read, daemon=True).start()
nextid = 0
latest = {}
def send(method, params, request=False):
    global nextid
    msg = {'jsonrpc':'2.0', 'method':method, 'params':params}
    if request:
        nextid += 1
        msg['id'] = nextid
    data = json.dumps(msg).encode()
    proc.stdin.write(f'Content-Length: {len(data)}\r\n\r\n'.encode()+data)
    proc.stdin.flush()
    return msg.get('id')
def await_reply(id):
    deadline = time.monotonic()+60
    while True:
        msg = messages.get(timeout=max(.01, deadline-time.monotonic()))
        if isinstance(msg, Exception):
            raise msg
        if msg.get('method') == 'textDocument/publishDiagnostics':
            p = msg['params']
            if p.get('isIncremental'):
                p['diagnostics'] = latest.get(p['uri'], {}).get('diagnostics', []) + p['diagnostics']
            latest[p['uri']] = p
        if 'method' in msg and 'id' in msg:
            response = json.dumps({'jsonrpc':'2.0','id':msg['id'],'result':None}).encode()
            proc.stdin.write(f'Content-Length: {len(response)}\r\n\r\n'.encode()+response)
            proc.stdin.flush()
            continue
        if msg.get('id') == id:
            if 'error' in msg:
                raise RuntimeError(msg)
            return msg
        if time.monotonic() >= deadline:
            raise TimeoutError('LSP timed out')
def check(version):
    await_reply(send('textDocument/waitForDiagnostics', {'uri':uri,'version':version}, True))
    diagnostics = latest.get(uri,{}).get('diagnostics',[])
    errors = [d for d in diagnostics if d.get('severity') == 1]
    if not diagnostics:
        raise AssertionError('expected verification info diagnostics; LSP check is inconclusive')
    print(json.dumps({'version':version, 'diagnostics':len(diagnostics), 'errors':errors}), flush=True)
    if errors:
        raise AssertionError('LSP reported verification errors')
def change(version, text):
    send('textDocument/didChange', {'textDocument':{'uri':uri,'version':version}, 'contentChanges':[{'text':text}]})
try:
    await_reply(send('initialize', {'processId':os.getpid(),'rootUri':root.as_uri(),'capabilities':{}}, True))
    send('initialized', {})
    send('textDocument/didOpen', {'textDocument':{'uri':uri,'languageId':'lean4','version':1,'text':source}})
    check(1)
    edited = source.replace('#gen_spec\n', '#gen_spec\n-- editor changed below cached generation\n', 1)
    change(2, edited)
    check(2)
    change(3, edited.split('veil module SecondModule')[0])
    check(3)
    change(4, source)
    check(4)
    for version in range(5,15):
        change(version, edited if version % 2 else source)
    check(14)
    print('Editor session checks passed.', flush=True)
    send('textDocument/didClose', {'textDocument':{'uri':uri}})
    await_reply(send('shutdown', None, True))
    send('exit', None)
    proc.wait(timeout=10)
finally:
    if proc.poll() is None:
        proc.terminate()
        try: proc.wait(timeout=5)
        except subprocess.TimeoutExpired: proc.kill()
    stderr.close()
