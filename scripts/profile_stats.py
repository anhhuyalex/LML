#!/usr/bin/env python3
"""Measure whole Lean declarations for the Exposition Stats tab."""
from __future__ import annotations

import argparse
import json
import math
import os
import pathlib
import platform
import select
import subprocess
import sys
import tempfile
import time
from collections import Counter, defaultdict

from website_stats.profiling import TRIALS, report_header
from website_stats.reader import require

PROTOCOL = "2026-07-28"
BEAM_REVISION = "8bcac69d31e4738542a8278af524a816b99b5400"
COMMAND_RANGES = pathlib.Path(__file__).resolve().parent / "website_stats/CommandRanges.lean"


class BeamError(ValueError):
    pass


class Beam:
    def __init__(self, binary, project):
        self.process = subprocess.Popen([binary], cwd=project, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, bufsize=0)
        self.workspace = {"root": str(project)}
        self.buffer = bytearray()
        self.request_id = 0
        os.set_blocking(self.process.stdin.fileno(), False)

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.process.stdin.close()
        try:
            self.process.wait(timeout=30)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait()
        finally:
            self.process.stdout.close()

    def request(self, method, params, deadline):
        self.request_id += 1
        message = {"jsonrpc": "2.0", "id": self.request_id, "method": method, "params": {
            **params, "_meta": {"io.modelcontextprotocol/protocolVersion": PROTOCOL,
                               "io.modelcontextprotocol/clientCapabilities": {}}}}
        remaining = memoryview((json.dumps(message) + "\n").encode())
        while remaining:
            _, writable, _ = select.select([], [self.process.stdin], [], max(0, deadline - time.monotonic()))
            if not writable:
                # A partial message cannot be followed by another request on this stream.
                raise OSError("Could not send a complete request to Beam")
            remaining = remaining[os.write(self.process.stdin.fileno(), remaining):]
        while deadline > time.monotonic():
            end = self.buffer.find(b"\n")
            if end == -1:
                ready, _, _ = select.select([self.process.stdout], [], [], max(0, deadline - time.monotonic()))
                if not ready:
                    break
                chunk = self.process.stdout.read(65536)
                if not chunk:
                    raise OSError("Beam closed its output")
                self.buffer.extend(chunk)
                continue
            reply = json.loads(self.buffer[:end])
            del self.buffer[:end + 1]
            if reply.get("id") != self.request_id:
                continue
            if "error" in reply:
                raise BeamError(str(reply["error"]))
            return reply["result"]
        raise TimeoutError("Beam request timed out")

    def call(self, name, arguments, deadline):
        reply = self.request("tools/call", {"name": name, "arguments": arguments}, deadline)
        if reply.get("isError"):
            raise BeamError(str(reply.get("structuredContent")))
        return reply["structuredContent"]

    def file_call(self, name, file, deadline, **arguments):
        return self.call(name, {"workspace": self.workspace, "path": file, **arguments}, deadline)

    def drop_workspace(self):
        try:
            self.call("lean_drop_workspace", {"workspace": self.workspace}, time.monotonic() + 30)
        except (BeamError, TimeoutError) as error:
            raise RuntimeError("Could not confirm that Beam stopped the previous request") from error

    def preflight(self, deadline):
        tools = self.request("tools/list", {}, deadline)["tools"]
        require(any(t["name"] == "lean_run_at" and "profile" in t["inputSchema"]["properties"]
                    for t in tools), "The selected Beam installation does not support profiling")
        identity = self.call("beam_version", {}, deadline)
        require(identity.get("source_commit") == BEAM_REVISION,
                "The Beam installation does not match the pinned source commit")
        return identity


def command_ranges(project, file, declarations, deadline):
    with tempfile.TemporaryDirectory(prefix="lml-command-ranges-") as temp:
        output = pathlib.Path(temp) / "commands.json"
        setup = pathlib.Path(temp) / "setup.json"
        with setup.open("w") as stream:
            subprocess.run(["lake", "setup-file", file], cwd=project, text=True,
                           stdout=stream, check=True,
                           timeout=max(0, min(deadline - time.monotonic(), 300)))
        subprocess.run(
            ["lake", "env", "lean", "--run", str(COMMAND_RANGES), file, str(setup), str(output)],
            input=json.dumps([d["id"] for d in declarations]) + "\n",
            cwd=project, text=True, stdout=subprocess.PIPE, check=True,
            timeout=max(0, min(deadline - time.monotonic(), 300)),
        )
        return {row["id"]: row for row in json.loads(output.read_text())}


def measure_file(beam, project, file, declarations, deadline):
    path = (project / file).resolve()
    require(path.is_relative_to(project) and path.suffix == ".lean", f"Invalid source path {file}")
    source = path.read_bytes()
    try:
        ranges = command_ranges(project, file, declarations, deadline)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        print(f"{file}: {error}", file=sys.stderr)
        if error.stdout:
            print(error.stdout[-2000:], file=sys.stderr)
        reason = "budget" if time.monotonic() >= deadline else "source_error"
        return {d["id"]: reason for d in declarations}

    shared = Counter((row["start"], row["end"]) for row in ranges.values())
    version = None
    readings = {}
    for d in declarations:
        key = d["id"]
        row = ranges.get(key)
        if time.monotonic() >= deadline:
            readings[key] = "budget"
        elif row is None:
            readings[key] = "no_command"
        elif shared[row["start"], row["end"]] != 1:
            readings[key] = "shared_command"
        else:
            snippet = source[row["start"]:row["end"]].decode()
            try:
                if version is None:
                    # Keep this document version for all three trials and other probes in the file.
                    version = beam.file_call(
                        "lean_update", file, min(deadline, time.monotonic() + 120))["version"]
                readings[key] = measure_command(beam, file, version, row, snippet, deadline)
            except TimeoutError:
                readings[key] = "budget" if time.monotonic() >= deadline else "timeout"
                beam.drop_workspace()
                version = None
    if version is not None:
        try:
            beam.file_call("lean_close", file, time.monotonic() + 30)
        except (BeamError, TimeoutError):
            beam.drop_workspace()
    require(path.read_bytes() == source, f"Source changed while profiling {file}")
    return readings


def measure_command(beam, file, version, row, snippet, deadline):
    readings = []
    for _ in range(TRIALS):
        try:
            result = beam.file_call(
                "lean_run_at", file, min(deadline, time.monotonic() + 120),
                version=version, line=row["line"], character=row["character"],
                text=snippet, profile=True,
            )
        except BeamError as error:
            print(f"{row['id']}: {error}", file=sys.stderr)
            return "beam_error"
        if result.get("success") is not True or result.get("proof_state") is not None:
            message = next((m.get("message") or m.get("text") for m in result.get("messages", [])
                            if isinstance(m, dict)), None)
            print(f"{row['id']}: {message or 'Beam did not complete the command'}", file=sys.stderr)
            return "rejected"
        elapsed = (result.get("profile") or {}).get("elapsed_ms")
        if type(elapsed) not in (int, float) or not math.isfinite(elapsed) or elapsed < 0:
            return "beam_error"
        readings.append(round(elapsed * 10))
    return readings


def profile(project, bundle, binary, seconds, pilot):
    build, declarations = bundle["build"], bundle["declarations"]
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=project, text=True).strip()
    require(build["revision"] == revision, "Catalog and checkout revisions differ")
    toolchain = (project / "lean-toolchain").read_text().strip()
    require(build["lean"] == toolchain, "Catalog and checkout Lean versions differ")
    require(not subprocess.check_output(
        ["git", "status", "--porcelain", "--untracked-files=no"], cwd=project),
        "Use a clean checkout to collect comparable timings")
    groups = defaultdict(list)
    for decl in sorted(declarations, key=lambda d: (d["file"], d["line"], d["id"])):
        groups[decl["file"]].append(decl)
    files = list(groups)
    selected_files = files if pilot is None else {
        files[i * len(files) // min(pilot, len(files))] for i in range(min(pilot, len(files)))
    }
    readings = {}
    deadline = time.monotonic() + seconds
    with Beam(binary, project) as beam:
        identity = beam.preflight(time.monotonic() + 30)
        for file, group in groups.items():
            if file not in selected_files:
                readings.update(dict.fromkeys((d["id"] for d in group), "pilot"))
            elif time.monotonic() >= deadline:
                readings.update(dict.fromkeys((d["id"] for d in group), "budget"))
            else:
                try:
                    timings = measure_file(beam, project, file, group, deadline)
                except (BeamError, TimeoutError) as error:
                    print(f"{file}: {error}", file=sys.stderr)
                    beam.drop_workspace()
                    timings = dict.fromkeys((d["id"] for d in group),
                                            "budget" if time.monotonic() >= deadline else "beam_error")
                readings.update(timings)
    counts = Counter(row if isinstance(row, str) else "measured" for row in readings.values())
    print(f"Profiled {counts['measured']} of {len(declarations)} declarations. Outcomes: {dict(counts)}")
    if pilot is not None:
        require(counts["measured"] > 0, "The Beam pilot returned no successful declaration timings")
    return {
        **report_header(build, declarations), "beam": identity["version"],
        "beam_revision": identity["source_commit"], "runner": f"{platform.platform()} ({os.cpu_count()} CPUs)",
        "mode": "pilot" if pilot is not None else "full", "readings": readings,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalog", type=pathlib.Path, required=True, help="Generated Stats data.json")
    parser.add_argument("--project", type=pathlib.Path, default=pathlib.Path.cwd())
    parser.add_argument("--beam", required=True, help="Path to the pinned lean-beam-mcp executable")
    parser.add_argument("--output", type=pathlib.Path, required=True)
    parser.add_argument("--seconds", type=int, default=14400)
    parser.add_argument("--pilot", type=int, metavar="FILES", help="Test a spread of this many files")
    args = parser.parse_args()
    try:
        require(args.seconds > 0 and (args.pilot is None or args.pilot > 0), "Use positive limits")
        bundle = json.loads(args.catalog.read_text())
        report = profile(args.project.resolve(), bundle, args.beam, args.seconds, args.pilot)
        args.output.write_text(json.dumps(report, sort_keys=True) + "\n")
    except (ValueError, KeyError, OSError, RuntimeError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Beam profiling failed: {error}\n")


if __name__ == "__main__":
    main()
