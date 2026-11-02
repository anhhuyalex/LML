"""Headless Chrome driver adapted from keithadler/leanviz tests/check_page.py.

Source commit: 1f80be49d0a8ee2210d62a86989f15035abcd083.
Copyright (c) 2026 Keith Adler. MIT license: LICENSE.browser.
Kept locally so Stats checks do not depend on a sibling checkout or network download.
"""
from __future__ import annotations

import base64
import json
import os
import pathlib
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import urllib.request

CANDIDATES = [
    os.environ.get("CHROME", ""),
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    "google-chrome", "google-chrome-stable", "chromium", "chromium-browser",
]


def find_chrome() -> str:
    for c in CANDIDATES:
        if c and (os.path.isfile(c) or shutil.which(c)):
            return c if os.path.isfile(c) else shutil.which(c)
    print("no Chrome or Chromium found; set CHROME=/path/to/chrome", file=sys.stderr)
    sys.exit(77)


class WS:
    """The smallest websocket client that can carry devtools messages: text frames, no extensions, no fragmentation."""

    def __init__(self, url: str) -> None:
        host, rest = url[5:].split("/", 1)
        host, port = host.split(":")
        self.sock = socket.create_connection((host, int(port)))
        key = base64.b64encode(b"0123456789abcdef").decode()
        self.sock.sendall(
            f"GET /{rest} HTTP/1.1\r\nHost: {host}:{port}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
            f"Sec-WebSocket-Key: {key}\r\nSec-WebSocket-Version: 13\r\n\r\n".encode())
        buf = b""
        while b"\r\n\r\n" not in buf:
            buf += self.sock.recv(4096)
        self.rest = buf.split(b"\r\n\r\n", 1)[1]
        self.id = 0
        self.events = []

    def send(self, method, params=None):
        self.id += 1
        payload = json.dumps({"id": self.id, "method": method, "params": params or {}}).encode()
        header = bytearray([0x81])
        n = len(payload)
        if n < 126:
            header.append(0x80 | n)
        elif n < 65536:
            header.append(0x80 | 126)
            header += n.to_bytes(2, "big")
        else:
            header.append(0x80 | 127)
            header += n.to_bytes(8, "big")
        self.sock.sendall(bytes(header) + b"\x00\x00\x00\x00" + payload)
        while True:
            msg = json.loads(self._frame())
            if msg.get("id") == self.id:
                return msg
            self.events.append(msg)

    def drain(self, seconds: float) -> None:
        self.sock.settimeout(seconds)
        try:
            while True:
                self.events.append(json.loads(self._frame()))
        except (TimeoutError, socket.timeout):
            pass
        finally:
            self.sock.settimeout(None)

    def _frame(self) -> bytes:
        def read(n: int) -> bytes:
            while len(self.rest) < n:
                chunk = self.sock.recv(65536)
                if not chunk:
                    raise ConnectionError("devtools closed the connection")
                self.rest += chunk
            out, self.rest = self.rest[:n], self.rest[n:]
            return out

        head = read(2)
        length = head[1] & 0x7F
        if length == 126:
            length = int.from_bytes(read(2), "big")
        elif length == 127:
            length = int.from_bytes(read(8), "big")
        return read(length)


class Page:
    def __init__(self, width: int = 1600, height: int = 1000, scale: int = 1) -> None:
        with socket.socket() as s:
            s.bind(("127.0.0.1", 0))
            port = s.getsockname()[1]
        self.dir = tempfile.mkdtemp()
        self.proc = subprocess.Popen(
            [find_chrome(), "--headless=new", "--disable-gpu", "--hide-scrollbars", "--no-first-run",
             "--no-sandbox", f"--force-device-scale-factor={scale}", f"--window-size={width},{height}",
             f"--remote-debugging-port={port}", f"--user-data-dir={self.dir}", "about:blank"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for _ in range(150):
            try:
                tabs = json.load(urllib.request.urlopen(f"http://127.0.0.1:{port}/json"))
                self.ws = WS(next(t for t in tabs if t["type"] == "page")["webSocketDebuggerUrl"])
                break
            except Exception:
                time.sleep(0.2)
        else:
            raise SystemExit("chrome did not start")
        self.ws.send("Runtime.enable")
        self.ws.send("Page.enable")

    def visit(self, url: str, ready: str, timeout: float = 60) -> None:
        self.ws.events.clear()
        self.ws.send("Page.navigate", {"url": url})
        deadline = time.time() + timeout
        while time.time() < deadline:
            time.sleep(0.25)
            r = self.ws.send("Runtime.evaluate", {"expression": ready, "returnByValue": True})
            if r.get("result", {}).get("result", {}).get("value") is True:
                return
        raise AssertionError(f"{url}: never satisfied `{ready}` within {timeout:.0f}s")

    def value(self, expression: str):
        r = self.ws.send("Runtime.evaluate", {"expression": expression, "returnByValue": True})
        return r.get("result", {}).get("result", {}).get("value")

    def screenshot(self, out: pathlib.Path) -> None:
        r = self.ws.send("Page.captureScreenshot", {"format": "png"})
        out.write_bytes(base64.b64decode(r["result"]["data"]))

    def problems(self):
        """Anything thrown or logged as an error, minus the favicon nobody has."""
        self.ws.drain(0.5)
        out: list = []
        for e in self.ws.events:
            if e.get("method") == "Runtime.exceptionThrown":
                d = e["params"]["exceptionDetails"]
                out.append(f"{d.get('text')}: {d.get('exception', {}).get('description', '')[:200]}")
            if e.get("method") == "Runtime.consoleAPICalled" and e["params"]["type"] == "error":
                text = " ".join(str(a.get("value", "")) for a in e["params"]["args"])
                if "favicon" not in text:
                    out.append(f"console.error: {text[:200]}")
        return out

    def close(self) -> None:
        self.proc.terminate()
        try:
            self.proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait()
        self.ws.sock.close()
        shutil.rmtree(self.dir, ignore_errors=True)

