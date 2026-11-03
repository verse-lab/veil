#!/usr/bin/env python3
"""Exercise VC manager checkpoint reuse through a real Lean language server.

Build VeilTest first, then run this script (Python standard library only).
--vc-manager and --multi-module select one regression; the default runs both.
The fixtures use ordinary @[veil] theorems, so no additional proof command is
required. Only virtual documents are edited; evidence is retained in /tmp.
"""

import argparse
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
        self.work = Path(tempfile.mkdtemp(prefix=f"veil-vc-manager-lsp-{label}-"))
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

    def check(self, uri, version, label):
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


def run_regression(multi_module):
    name = "VCManagerMultiModuleIncrementality" if multi_module else "VCManagerIncrementality"
    fixture = ROOT / "VeilTest" / "Regression" / f"{name}.lean"
    uri = fixture.as_uri()
    source = fixture.read_text()
    server = LeanServer("multi" if multi_module else "single")
    try:
        server.send("initialize", {"processId": None, "rootUri": ROOT.as_uri(), "capabilities": {}}, True)
        server.send("initialized", {})
        if multi_module:
            server.open(uri, source)
            server.check(uri, 1, "fresh multi-module file")
            old = "  unveil\n  done\n"
            assert source.count(old) == 1, "missing unique first-module proof"
            source = source.replace(old, "  unveil\n  skip\n  done\n", 1)
            server.change(uri, 2, source)
            server.check(uri, 2, "edit proof in first module")
        else:
            start = source.index("-- BEGIN STEP PROOF\n")
            end = source.index("-- END STEP PROOF\n") + len("-- END STEP PROOF\n")
            without_proof = source[:start] + source[end:]
            # Establish that a missing manual proof is valid on a fresh open.
            server.open(uri, without_proof)
            server.check(uri, 1, "fresh file without proof")
            server.change(uri, 2, source)
            server.check(uri, 2, "insert proof")
            # #gen_spec and the initializer stay unchanged. The restored
            # checkpoint must not reuse the deleted step theorem as a witness.
            server.change(uri, 3, without_proof)
            server.check(uri, 3, "delete proof in one module")
        print(f"PASS: {name}", flush=True)
    finally:
        server.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--vc-manager", action="store_true")
    modes.add_argument("--multi-module", action="store_true")
    args = parser.parse_args()
    if not args.multi_module:
        run_regression(False)
    if not args.vc_manager:
        run_regression(True)


if __name__ == "__main__":
    main()
