"""Lean LSP client shared by the incremental elaboration regressions."""

import json
import os
import queue
import signal
import subprocess
import tempfile
import threading
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


class LeanServer:
    def __init__(self, label):
        self.work = Path(tempfile.mkdtemp(prefix=f"veil-lsp-{label}-"))
        print(f"{label} evidence: {self.work}", flush=True)
        self.stderr = (self.work / "server.stderr").open("w")
        self.proc = subprocess.Popen(
            ["lake", "serve"], cwd=ROOT, stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=self.stderr, start_new_session=True,
        )
        self.messages = queue.Queue()
        self.notifications = []
        self.next_id = 0
        threading.Thread(target=self.read_messages, daemon=True).start()

    def read_messages(self):
        try:
            while True:
                headers = {}
                while True:
                    line = self.proc.stdout.readline()
                    if not line:
                        self.messages.put({"eof": True})
                        return
                    if line in (b"\r\n", b"\n"):
                        break
                    key, value = line.decode().split(":", 1)
                    headers[key.lower()] = value.strip()
                length = int(headers["content-length"])
                self.messages.put(json.loads(self.proc.stdout.read(length)))
        except Exception as ex:
            self.messages.put({"reader_error": repr(ex)})

    def write(self, message):
        data = json.dumps(message).encode()
        self.proc.stdin.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
        self.proc.stdin.flush()

    def send(self, method, params, request=False):
        message = {"jsonrpc": "2.0", "method": method, "params": params}
        if request:
            self.next_id += 1
            message["id"] = self.next_id
        self.write(message)
        if not request:
            return
        deadline = time.monotonic() + 180
        while True:
            response = self.messages.get(timeout=max(0, deadline - time.monotonic()))
            if response.get("eof") or response.get("reader_error"):
                raise RuntimeError(f"{response}\n{(self.work / 'server.stderr').read_text()}")
            if "method" in response and "id" in response:
                self.write({"jsonrpc": "2.0", "id": response["id"], "result": None})
            elif response.get("id") == message["id"]:
                if "error" in response:
                    raise RuntimeError(response)
                return response.get("result")
            else:
                self.notifications.append(response)

    def diagnostics(self, uri, version, label):
        self.send("textDocument/waitForDiagnostics", {"uri": uri, "version": version}, True)
        (self.work / f"notifications-{version}.json").write_text(
            json.dumps(self.notifications, indent=2)
        )
        publications = [
            n["params"] for n in self.notifications
            if n.get("method") == "textDocument/publishDiagnostics"
            and n["params"].get("uri") == uri
            and n["params"].get("version") == version
        ]
        assert publications, f"{label}: missing diagnostics for document version {version}"
        diagnostics = publications[-1]["diagnostics"]
        print(f"{label}: {json.dumps(diagnostics, ensure_ascii=False)}", flush=True)
        return diagnostics

    def check(self, uri, version, label):
        diagnostics = self.diagnostics(uri, version, label)
        problems = [d for d in diagnostics if d.get("severity") in (1, 2)]
        assert not problems, f"{label}: {problems}"

    def open(self, uri, source):
        self.send("textDocument/didOpen", {"textDocument": {
            "uri": uri, "languageId": "lean4", "version": 1, "text": source,
        }})

    def change(self, uri, version, source):
        self.send("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": version},
            "contentChanges": [{"text": source}],
        })

    def close(self):
        # Let the server close its file workers on EOF before stopping Lake.
        self.proc.stdin.close()
        try:
            self.proc.wait(timeout=15)
        except subprocess.TimeoutExpired:
            # Lake is a wrapper; its Lean server and workers share this group.
            try:
                os.killpg(self.proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            self.proc.wait()
        self.stderr.close()
