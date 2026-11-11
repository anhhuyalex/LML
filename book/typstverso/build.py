#!/usr/bin/env python3
# Copyright 2026 Shreyas Srinivas
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Incrementally extract requested Lean code and export a Typst document.

Vendored from https://github.com/Shreyas4991/TypstVerso (see ../VENDORED.md).
Changes for LML are marked "LML:" and listed in ../VENDORED.md.
"""
import argparse
from contextlib import contextmanager
import errno
import hashlib
import html
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT / "LeanProject"
DOCUMENT = ROOT / "documents/slides"
LIBRARY = ROOT / "typst"
TEMPLATES = ROOT / "templates/html"
DOCUMENT_KINDS = ("slides", "article", "book", "blog")
BUILD = DOCUMENT / "build"
MODULES = ["LeanProject"]
CACHE_FORMAT = 1  # LML: change when lean.json's content or the requests it answers change
EXPORT_SCRIPT = ROOT / "ExportLean.lean"  # LML: kept next to build.py, not in the Lean project
REQUEST_PREFIX = "LEAN_REQUEST:"


class ProcessFailure(subprocess.CalledProcessError):
    def __str__(self):
        return (self.stderr or self.stdout or "").strip() or super().__str__()


def run(args, cwd=PROJECT, capture=False, env=None, input=None):
    command = [str(a) for a in args]
    result = subprocess.run(command, cwd=cwd, text=True, input=input,
                            stdout=subprocess.PIPE if capture else None,
                            stderr=subprocess.PIPE if capture else None, env=env)
    if result.returncode:
        raise ProcessFailure(result.returncode, command, output=result.stdout, stderr=result.stderr)
    if capture and result.stderr:
        print(result.stderr, end="", file=sys.stderr)
    return result.stdout


@contextmanager
def build_lock(library):
    """Serialize builders sharing data; the OS releases this lock after a crash."""
    library.mkdir(parents=True, exist_ok=True)
    with (library / ".build.lock").open("a+b") as lock:
        if os.name == "nt":
            import msvcrt
            if lock.seek(0, os.SEEK_END) == 0:
                lock.write(b"0")
                lock.flush()
            waiting = False
            while True:
                lock.seek(0)
                try:
                    msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
                    break
                except OSError as error:
                    if error.errno not in {errno.EACCES, errno.EAGAIN, errno.EDEADLK}:
                        raise
                    if not waiting:
                        print("Waiting for another build to finish...", flush=True)
                        waiting = True
                    time.sleep(0.1)
            try:
                yield
            finally:
                lock.seek(0)
                msvcrt.locking(lock.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            import fcntl
            try:
                fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                print("Waiting for another build to finish...", flush=True)
                fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(lock.fileno(), fcntl.LOCK_UN)


def compact_cache(data):
    """LML: store each distinct tooltip once.

    Signatures repeat the same long tooltips (a constant's type and docstring) thousands
    of times. Tokens keep a table index ``t`` instead of the ``tooltip`` text; ``lean.typ``
    looks it up in ``tooltips``. ``expand_cache`` is the inverse.
    """
    table, index = [], {}

    def visit(node):
        if isinstance(node, list):
            return [visit(item) for item in node]
        if not isinstance(node, dict):
            return node
        result = {}
        for key, value in node.items():
            if key == "tooltip" and isinstance(value, str):
                result["t"] = index.setdefault(value, len(index))
                if result["t"] == len(table):
                    table.append(value)
            else:
                result[key] = visit(value)
        return result

    compact = visit(data)
    compact["tooltips"] = table
    return compact


def expand_cache(data):
    """LML: inverse of ``compact_cache`` (accepts data that was never compacted)."""
    table = data.get("tooltips")
    if table is None:
        return data

    def visit(node):
        if isinstance(node, list):
            return [visit(item) for item in node]
        if not isinstance(node, dict):
            return node
        result = {}
        for key, value in node.items():
            if key == "t" and isinstance(value, int):
                result["tooltip"] = table[value]
            else:
                result[key] = visit(value)
        return result

    expanded = visit({k: v for k, v in data.items() if k != "tooltips"})
    return expanded


def write_json(path, value):
    """Atomically replace the single extraction/cache file, only when it changes."""
    path.parent.mkdir(parents=True, exist_ok=True)
    # LML: compact separators and a shared tooltip table keep lean.json loadable by Typst.
    content = json.dumps(compact_cache(value), ensure_ascii=False, separators=(",", ":")) + "\n"
    if path.is_file() and path.read_text() == content:
        return
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", prefix=".lean-", suffix=".tmp",
                                     dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(content)
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def quote_lines(fragments):
    """Keep whitespace and semantic tokens; omit doc comments from displayed code."""
    lines = [[]]
    for fragment in fragments:
        if fragment["kind"] == "doc-comment":
            continue
        if fragment["kind"] == "state":
            lines[-1].append(fragment)
            continue
        for i, part in enumerate(fragment["text"].split("\n")):
            if i:
                lines.append([])
            if part:
                lines[-1].append({**fragment, "text": part})
    def blank(line):
        return all(p["kind"] != "state" and not p["text"].strip() for p in line)
    while lines and blank(lines[0]):
        lines.pop(0)
    while lines and blank(lines[-1]):
        lines.pop()
    return lines


def prepare_subverso(project=None):
    project = PROJECT if project is None else project
    package = project / ".lake/packages/subverso"
    patch = project / "subverso.patch"
    if not package.is_dir():
        raise RuntimeError("Fetch dependencies first: run lake update in " + str(project))
    applied = subprocess.run(["git", "apply", "--reverse", "--check", str(patch)],
                             cwd=package, capture_output=True, text=True)
    if applied.returncode == 0:
        return
    check = subprocess.run(["git", "apply", "--check", str(patch)],
                           cwd=package, capture_output=True, text=True)
    if check.returncode:
        raise RuntimeError("Cannot apply subverso.patch: " + check.stderr.strip())
    run(["git", "apply", patch], cwd=package)


def config_snapshot(project):
    """LML: the files that pin a prebuilt Lean project (toolchain and dependency revisions).

    Contents are hashed, not modification times: a fresh checkout (CI) must give the same key.
    """
    paths = []
    for name in ("lake-manifest.json", "lean-toolchain", "lakefile.toml"):
        path = project / name
        if path.is_file():
            paths.append((name, hashlib.sha256(path.read_bytes()).hexdigest()))
    return paths


def newest_lean_source(project):
    """LML: modification time of the newest ``.lean`` file below ``project`` (nanoseconds)."""
    newest = 0
    for directory, dirs, files in os.walk(project):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake", ".venv", "node_modules", "__pycache__"}]
        for name in files:
            if name.endswith(".lean"):
                newest = max(newest, (Path(directory) / name).stat().st_mtime_ns)
    return newest


def source_snapshot(project):
    """Include dependency sources; exclude compiled artifacts and nested caches."""
    paths = []
    for base in (project, project / ".lake/packages"):
        for directory, dirs, files in os.walk(base):
            dirs[:] = sorted(d for d in dirs if d not in {
                ".git", ".lake", ".venv", "node_modules", "__pycache__"})
            for name in sorted(files):
                if (name.endswith((".lean", ".patch")) or
                        name in {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}):
                    path = Path(directory) / name
                    try:
                        stat = path.stat()
                    except FileNotFoundError:
                        continue
                    paths.append((str(path.relative_to(project)), stat.st_mtime_ns, stat.st_size))
    return sorted(paths)


def request_key(request):
    return json.dumps(request, ensure_ascii=False, sort_keys=True)


def request_description(request):
    if request["kind"] == "declaration":
        return "the Lean definition or proof " + json.dumps(request["name"], ensure_ascii=False)
    description = "the Lean command " + json.dumps(request["source"], ensure_ascii=False)
    if request.get("module") is not None:
        description += " from " + json.dumps(request["module"], ensure_ascii=False)
    return description


def recovery_error(request):
    return ("Error: The result for " + request_description(request) + " is still missing after a rebuild.\n\n"
            "Probable cause: The saved Lean results could not be updated, or this document is reading a different copy.\n\n"
            "Probable fix: Check the build.py terminal for errors. From the folder containing build.py, run:\n"
            ".venv/bin/python build.py --all --refresh\n"
            "Then keep it running with:\n.venv/bin/python build.py --watch --all")


def validate_request(request):
    if not isinstance(request, dict):
        raise ValueError("Invalid Lean extraction request")
    if request.get("kind") == "declaration" and isinstance(request.get("name"), str):
        return {"kind": "declaration", "name": request["name"]}
    if request.get("kind") == "command" and isinstance(request.get("source"), str):
        module = request.get("module")
        if module is not None and not isinstance(module, str):
            raise ValueError("Lean command module must be a string")
        return {"kind": "command", "source": request["source"].strip(), "module": module}
    raise ValueError("Invalid Lean extraction request: " + repr(request))


class TypstFailure(RuntimeError):
    def __init__(self, result):
        self.diagnostics = result.stderr
        super().__init__(result.stderr.strip())

    def missing_request(self):
        decoder = json.JSONDecoder()
        for line in self.diagnostics.splitlines():
            if "error:" not in line:
                continue
            try:
                message = line.split("error:", 1)[1].strip()
                for wrapper in ("assertion failed: ", "panicked with: "):
                    if message.startswith(wrapper):
                        message = message[len(wrapper):]
                for prefix, kind in (("Error: The Lean definition or proof ", "declaration"),
                                     ("Error: The Lean command ", "command")):
                    if not message.startswith(prefix):
                        continue
                    payload = message[len(prefix):]
                    value, end = decoder.raw_decode(payload)
                    if kind == "declaration":
                        return validate_request({"kind": kind, "name": value})
                    module = None
                    rest = payload[end:]
                    if " Lean file: " in rest:
                        module, _ = decoder.raw_decode(rest.split(" Lean file: ", 1)[1])
                    return validate_request({"kind": kind, "source": value, "module": module})
                # Older copies of lean.typ used a JSON diagnostic. New messages
                # are readable sentences, with quoted names sufficient for recovery.
                if REQUEST_PREFIX in line:
                    request, _ = decoder.raw_decode(line.split(REQUEST_PREFIX, 1)[1])
                    return validate_request(request)
            except (ValueError, TypeError):
                continue
        return None


class Builder:
    def __init__(self, project=PROJECT, document=DOCUMENT, output=None,
                 modules=None, refresh=False, formats="both", library=LIBRARY,
                 templates=TEMPLATES, kind=None, prebuilt=False, export_script=EXPORT_SCRIPT,
                 light_pdf=False, jobs=1):
        # LML: `prebuilt` means the Lean project is already built (and is not ours to
        # patch): skip `lake update`, the SubVerso patch and `lake build`.
        self.prebuilt = prebuilt
        self.light_pdf = light_pdf
        self.jobs = max(1, jobs)
        self.recovery_lock = threading.Lock()  # recovery edits the shared extraction cache
        self.export_script = Path(export_script).resolve()
        self.project = Path(project).resolve()
        self.document = Path(document).resolve()
        self.library = Path(library).resolve()
        self.root = Path(os.path.commonpath([self.document, self.library]))
        self.templates = Path(templates).resolve()
        self.kind = kind or (self.document.name if self.document.name in DOCUMENT_KINDS else "article")
        if self.kind not in DOCUMENT_KINDS:
            raise ValueError("Unknown document template: " + self.kind)
        self.output = Path(output).resolve() if output is not None else self.document / "build"
        self.modules = list(MODULES if modules is None else modules)
        if not self.modules or any(not re.fullmatch(r"[\w']+(?:\.[\w']+)*", m)
                                   for m in self.modules):
            raise ValueError("Provide valid Lean module names with --module")
        self.formats = formats
        self.path = self.library / "lean.json"
        self.refresh = refresh
        self.load_cache(refresh)

    def load_cache(self, refresh=False):
        self.ready = False
        self.built_modules = set()
        self.env = None
        self.data = {"schemaVersion": 1, "declarations": {}, "commands": [], "inlineCommands": []}
        self.fingerprint = self.lean_fingerprint()
        if self.path.is_file() and not refresh:
            try:
                saved = expand_cache(json.loads(self.path.read_text()))
                if (saved.get("schemaVersion") == 1 and
                        saved.get("_cache", {}).get("fingerprint") == self.fingerprint and
                        isinstance(saved.get("declarations"), dict) and
                        isinstance(saved.get("commands"), list) and
                        isinstance(saved.get("inlineCommands"), list)):
                    self.data = saved
            except (ValueError, AttributeError):
                print("Discarding invalid extraction cache: " + str(self.path), file=sys.stderr)

    def warn_if_stale(self):
        """LML: remind the user that cached signatures predate edits to the Lean sources."""
        if os.environ.get("CI"):
            return  # a fresh checkout is always newer than a restored cache; the cache key covers it
        if self.prebuilt and self.path.is_file() and newest_lean_source(self.project) > self.path.stat().st_mtime_ns:
            print("Warning: Lean sources are newer than the saved signatures; run with --refresh "
                  "to extract them again.", file=sys.stderr)

    def lean_fingerprint(self):
        # LML: a prebuilt run extracts through ExportLean.lean only, so editing the rest of this
        # script (HTML export, CLI) must not discard minutes of Lean results. Bump
        # CACHE_FORMAT when the stored data or the requests change.
        digest = hashlib.sha256(Path(__file__).read_bytes() if not self.prebuilt
                                else f"cache-format-{CACHE_FORMAT}".encode())
        digest.update(self.export_script.read_bytes())
        # LML: a prebuilt project is described by its pins; hashing its (concurrently edited)
        # sources would invalidate the cache on every edit. `warn_if_stale` covers that case.
        snapshot = config_snapshot(self.project) if self.prebuilt else source_snapshot(self.project)
        digest.update(request_key({"project": str(self.project), "modules": self.modules,
                                   "sources": snapshot}).encode())
        return digest.hexdigest()

    def save(self):
        if self.lean_fingerprint() != self.fingerprint:
            raise RuntimeError("Lean inputs changed during extraction; rebuild to use the updated sources")
        self.data["_cache"] = {"fingerprint": self.fingerprint}
        write_json(self.path, self.data)

    def prepare(self, extra_modules=()):
        targets = set(self.modules) | set(extra_modules)
        if self.ready and targets <= self.built_modules:
            return
        if self.prebuilt:
            sysroot = run(["lake", "env", "lean", "--print-prefix"],
                          cwd=self.project, capture=True).strip()
            self.env = {**os.environ, "LEAN_SYSROOT": sysroot}
            self.built_modules.update(targets)
            self.ready = True
            return
        if not (self.project / ".lake/packages/subverso").is_dir():
            run(["lake", "update"], cwd=self.project)
        prepare_subverso(self.project)
        fingerprint = self.lean_fingerprint()
        if fingerprint != self.fingerprint and "_cache" in self.data:
            raise RuntimeError("Lean inputs changed during the build; rebuild to use the updated sources")
        # Fetching dependencies and applying the patch intentionally change inputs.
        # Capture them before building, so later editor changes cannot bless stale data.
        self.fingerprint = fingerprint
        run(["lake", "build", "subverso-extract-mod", "+SubVerso.Signature",
             *["+" + m for m in sorted(targets - self.built_modules)]], cwd=self.project)
        sysroot = run(["lake", "env", "lean", "--print-prefix"],
                      cwd=self.project, capture=True).strip()
        self.env = {**os.environ, "LEAN_SYSROOT": sysroot}
        self.built_modules.update(targets)
        self.ready = True

    def bridge(self, arguments, value):
        result = run(["lake", "env", "lean", "--run", self.export_script, *arguments],
                     cwd=self.project, capture=True, env=self.env,
                     input=value if isinstance(value, str) else json.dumps(value))
        return json.loads(result)

    def extract_declarations(self, names):
        self.prepare()
        resolved = self.bridge(["--resolve"], {"modules": self.modules, "declarations": names})
        groups = {}
        for name in names:
            groups.setdefault(resolved[name], []).append(name)
        for module, selected in sorted(groups.items()):
            print(f"Extracting {len(selected)} declaration(s) from {module}", flush=True)
            flags = [arg for name in selected for arg in ("--declaration", name)]
            executable = self.project / ".lake/packages/subverso/.lake/build/bin/subverso-extract-mod"
            raw = run(["lake", "env", executable, *flags, module], cwd=self.project,
                      capture=True, env=self.env)
            decoded = self.bridge(["--decode", module, *selected], raw)
            for name in selected:
                declaration = decoded["declarations"].get(name)
                if declaration is None:
                    raise RuntimeError("No source declaration extracted for " + name)
                self.data["declarations"][name] = {
                    "module": module, "source": declaration["source"],
                    "signature": declaration["signature"],
                    "signatureFragments": declaration["signatureFragments"],
                    "lines": quote_lines(declaration["fragments"])}

    def ensure_requests(self, requests):
        normalized = {request_key(r): r for r in map(validate_request, requests)}
        missing = sorted({r["name"] for r in normalized.values()
                          if r["kind"] == "declaration" and
                          r["name"] not in self.data["declarations"]})
        pending = [r for r in normalized.values() if r["kind"] == "command" and not any(
            c["source"] == r["source"] and c["module"] == r["module"]
            for c in self.data["inlineCommands"])]
        if missing:
            self.extract_declarations(missing)
        if pending:
            self.prepare(r["module"] for r in pending if r["module"] is not None)
            print(f"Evaluating {len(pending)} Lean command(s)", flush=True)
            groups = {}
            for request in pending:
                groups.setdefault(request["module"], []).append(request)
            commands = []
            for module, requests in groups.items():
                # Importing Mathlib registers global Lean extensions. Reusing an
                # older environment afterwards can panic inside Lean. Keep distinct
                # import contexts in separate processes, including their initial import.
                commands.extend(self.bridge(["--commands"], {
                    "modules": self.modules if module is None else [module], "commands": requests}))
            for command in commands:
                self.data["inlineCommands"].append({
                    "module": command["module"], "source": command["source"],
                    "lines": quote_lines(command["fragments"]),
                    # LML: the raw fragments duplicate `lines` and are not needed by Typst.
                    "messages": [{**{k: v for k, v in m.items() if k != "fragments"},
                                  "lines": quote_lines(m["fragments"])}
                                 for m in command["messages"]]})
        self.save()
        return bool(missing or pending)

    def typst(self, arguments):
        result = subprocess.run(["typst", *map(str, arguments), "--root", str(self.root),
                                 "--diagnostic-format", "short"],
                                cwd=self.document, capture_output=True, text=True)
        if result.returncode:
            raise TypstFailure(result)
        if result.stderr:
            print(result.stderr, end="", file=sys.stderr)
        return result.stdout

    def discover(self, entry):
        expression = '''query(metadata).filter(item => type(item.value) == dictionary and
          item.value.at("kind", default: "") == "lean-request").map(item => item.value.request)'''
        return json.loads(self.typst(["eval", expression, "--in", entry,
                                      "--input", "lean-discover=true"]))

    def export(self, entry):
        self.output.mkdir(parents=True, exist_ok=True)
        stem = entry.stem
        with tempfile.TemporaryDirectory(prefix="export-", dir=self.output) as temporary:
            directory = Path(temporary)
            targets = []
            if self.formats in {"pdf", "both"}:
                # LML: a "light" PDF drops everything that only the HTML or an interactive PDF
                # needs: Lean hover boxes, and the per-glyph accessibility tags that made a
                # whole book of signatures ten times larger.
                light = ["--input", "lean-plain=true", "--no-pdf-tags"] if self.light_pdf else []
                self.typst(["compile", *light, entry, directory / "document.pdf"])
            if self.formats in {"html", "both"}:
                self.typst(["compile", "--format", "svg", entry, directory / "page-{n}.svg"])
            expression = '''query(metadata).filter(item => type(item.value) == dictionary and
              item.value.at("kind", default: "") == "lean-hover").map(item => {
              let p = item.location().position()
              (page: p.page, x: p.x.pt(), y: p.y.pt(), ..item.value)
            })'''
            needs_regions = self.formats != "pdf" or not self.light_pdf
            regions = json.loads(self.typst(["eval", expression, "--in", entry])) if needs_regions else []
            # LML: link regions (cross-references) and anchors (link targets) for the HTML reader.
            navigation_expression = '''query(metadata).filter(item => type(item.value) == dictionary and
              item.value.at("kind", default: "") in ("book-link", "book-anchor")).map(item => {
              let p = item.location().position()
              (page: p.page, x: p.x.pt(), y: p.y.pt(), ..item.value)
            })'''
            navigation = json.loads(self.typst(["eval", navigation_expression, "--in", entry])) if needs_regions else []
            if self.formats in {"html", "both"}:
                # Ask Typst for outlined headings and their final locations, including
                # computed chapter numbers; never infer a contents list from page text.
                outline_expression = '''
                  let plain(body) = {
                    if type(body) == str { body }
                    else if type(body) == content {
                      if (body.func() == [ ].func() or body.func() == linebreak
                        or body.func() == parbreak or body.func() == h) { " " }
                      else if body.has("text") { body.text }
                      else if body.has("children") { body.children.map(plain).join() }
                      else if body.has("body") { plain(body.body) }
                      else { "" }
                    } else { "" }
                  }
                  query(heading).filter(h => h.outlined).map(h => {
                    let p = h.location().position()
                    let n = if h.numbering == none { "" }
                      else { plain(numbering(h.numbering, ..counter(heading).at(h.location()))) }
                    (level: h.level, title: if n == "" { plain(h.body) }
                      else { n + " " + plain(h.body) },
                      page: p.page, y: p.y.pt())
                  })'''
                headings = json.loads(self.typst(["eval", outline_expression, "--in", entry]))
                for index, heading in enumerate(headings, 1):
                    heading["id"] = f"heading-{index}"
                pages = []
                svgs = sorted(directory.glob("page-*.svg"), key=lambda p: int(p.stem.split("-")[-1]))
                for number, svg in enumerate(svgs, 1):
                    markup = svg.read_text()
                    width, height = re.search(r'viewBox="0 0 ([\d.]+) ([\d.]+)"', markup).groups()
                    pages.append({"svg": markup, "width": float(width), "height": float(height),
                                  "regions": [r for r in regions if r["page"] == number],
                                  "links": [n for n in navigation if n["page"] == number and n["kind"] == "book-link"],
                                  "anchors": [n for n in navigation if n["page"] == number and n["kind"] == "book-anchor"],
                                  "headings": [h for h in headings if h["page"] == number]})
                template = (self.templates / (self.kind + ".html")).read_text()
                for marker, name in (("__TOOLTIPS_CSS__", "tooltips.css"),
                                     ("__TOOLTIPS_JS__", "tooltips.js"),
                                     ("__BLOG_JS__", "blog.js"),
                                     ("__READER_JS__", "reader.js")):
                    if marker in template:
                        template = template.replace(marker, (self.templates / name).read_text())
                payload = json.dumps(pages, ensure_ascii=False).replace("<", "\\u003c")
                document = template.replace("__DOCUMENT_DATA__", payload).replace("__TITLE__", html.escape(stem))
                (directory / "document.html").write_text(document)
                targets.append((directory / "document.html", self.output / (stem + ".html")))
            if self.formats in {"pdf", "both"}:
                # LML: a whole book of signatures has hundreds of thousands of hover regions;
                # PDF viewers cannot cope with that many annotations, so they can be skipped.
                if not self.light_pdf:
                    annotate_pdf(directory / "document.pdf", directory / "annotated.pdf", regions)
                    targets.append((directory / "annotated.pdf", self.output / (stem + ".pdf")))
                else:
                    targets.append((directory / "document.pdf", self.output / (stem + ".pdf")))
            for source, destination in targets:
                source.replace(destination)
            print("Built " + ", ".join(str(p) for _, p in targets) +
                  f" ({len(regions)} Lean hover regions)", flush=True)

    def build(self, entries="main.typ", extract_only=False):
        """Build one entry file, or several that share a single Lean extraction pass."""
        with build_lock(self.library):
            # A different process may have updated the data while this one waited.
            self.load_cache(self.refresh)
            self.refresh = False
            self.warn_if_stale()
            self.build_locked(entries, extract_only)

    def resolve_entry(self, entry):
        entry = (self.document / entry).resolve()
        if not entry.is_file() or not entry.is_relative_to(self.document):
            raise ValueError("The entry file must be inside the document project: " + str(entry))
        return entry

    def build_locked(self, entries="main.typ", extract_only=False):
        # LML: all entries are discovered first, so Lean runs once for the union of requests.
        entries = [entries] if isinstance(entries, (str, os.PathLike)) else list(entries)
        resolved = [self.resolve_entry(entry) for entry in entries]
        requests = [request for entry in resolved for request in self.discover(entry)]
        self.ensure_requests(requests)
        if extract_only:
            return
        if self.jobs == 1 or len(resolved) == 1:
            for entry in resolved:
                self.export_with_recovery(entry)
        else:
            # LML: entries are independent Typst runs; export them in parallel.
            with ThreadPoolExecutor(self.jobs) as pool:
                for _ in pool.map(self.export_with_recovery, resolved):
                    pass  # iterating re-raises the first failure

    def export_with_recovery(self, entry):
        attempted = set()
        for _ in range(32):
            try:
                self.export(entry)
                return
            except TypstFailure as error:
                request = error.missing_request()
                if request is None:
                    raise
                key = request_key(request)
                if key in attempted:
                    raise RuntimeError(recovery_error(request)) from error
                attempted.add(key)
                print("Preparing the missing result for " + request_description(request) + " and rebuilding...", flush=True)
                with self.recovery_lock:
                    prepared = self.ensure_requests([request])
                if not prepared:
                    raise RuntimeError(recovery_error(request)) from error
        raise RuntimeError("Stopped after 32 missing-data retries; check document-dependent requests")


def annotate_pdf(source, target, regions):
    try:
        from pypdf import PdfReader, PdfWriter
        from pypdf.generic import (ArrayObject, DecodedStreamObject, DictionaryObject, FloatObject,
                                   NameObject, NumberObject, TextStringObject)
    except ImportError:
        raise RuntimeError("Install PDF support: .venv/bin/python -m pip install -r requirements.txt") from None
    writer = PdfWriter()
    writer.clone_document_from_reader(PdfReader(source))
    for region in regions:
        page = writer.pages[region["page"] - 1]
        x, y = region["x"], float(page.mediabox.height) - region["y"]
        w, h = region["width"], region["height"]
        appearance = DecodedStreamObject()
        appearance.set_data(b"")
        appearance.update({NameObject("/Type"): NameObject("/XObject"),
                           NameObject("/Subtype"): NameObject("/Form"),
                           NameObject("/BBox"): ArrayObject([FloatObject(v) for v in (0, 0, w, h)]),
                           NameObject("/Resources"): DictionaryObject()})
        annotation = DictionaryObject({
            NameObject("/Type"): NameObject("/Annot"),
            NameObject("/Subtype"): NameObject("/Text"),
            NameObject("/Rect"): ArrayObject([FloatObject(v) for v in (x, y - h, x + w, y)]),
            NameObject("/Contents"): TextStringObject(region["tooltip"]),
            NameObject("/T"): TextStringObject("Lean proof state" if region["role"] == "state" else "Lean"),
            # Invisible appearance preserves the typeset token/bubble; contents remain clickable.
            NameObject("/Name"): NameObject("/Comment"),
            NameObject("/F"): NumberObject(0),
            NameObject("/AP"): DictionaryObject({NameObject("/N"): writer._add_object(appearance)}),
        })
        writer.add_annotation(region["page"] - 1, annotation)
    with target.open("wb") as stream:
        writer.write(stream)


def watch_snapshot(project, document, library=LIBRARY, templates=TEMPLATES, include_packages=True):
    paths = [(str(Path(__file__)), Path(__file__).stat().st_mtime_ns, Path(__file__).stat().st_size)]
    paths += source_snapshot(project) if include_packages else config_snapshot(project)
    documents = [document] if isinstance(document, (str, os.PathLike)) else document
    for root in documents:
        for directory, dirs, files in os.walk(root):
            dirs[:] = sorted(d for d in dirs if d not in {".git", ".venv", "build", "__pycache__"})
            for name in sorted(files):
                if name == "lean.json":
                    continue
                path = Path(directory) / name
                try:
                    stat = path.stat()
                except FileNotFoundError:
                    continue
                paths.append((str(path), stat.st_mtime_ns, stat.st_size))
    for base in (library, templates):
        for path in sorted(Path(base).rglob("*")):
            if path.is_file() and path.name not in {"lean.json", ".build.lock"} and path.suffix != ".tmp":
                try:
                    stat = path.stat()
                except FileNotFoundError:
                    continue
                paths.append((str(path), stat.st_mtime_ns, stat.st_size))
    return paths


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("entries", nargs="*", default=["main.typ"], metavar="entry",
                        help="Typst entry files, relative to the document folder")
    parser.add_argument("--project", type=Path, default=PROJECT)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--document", type=Path, default=DOCUMENT)
    selection.add_argument("--all", action="store_true", help="Build slides, article, book, and blog")
    parser.add_argument("--output", type=Path, help="Output directory (default: DOCUMENT/build)")
    parser.add_argument("--library", type=Path, default=LIBRARY, help="Shared lean.typ and extraction cache")
    parser.add_argument("--templates", type=Path, default=TEMPLATES, help="HTML template directory")
    parser.add_argument("--template", choices=DOCUMENT_KINDS, help="Browser layout (inferred from document folder)")
    parser.add_argument("--module", action="append", dest="modules", help="Lean environment to import (repeatable)")
    parser.add_argument("--format", choices=["html", "pdf", "both"], default="both")
    parser.add_argument("--extract-only", action="store_true")
    parser.add_argument("--refresh", action="store_true", help="Discard the extraction cache once")
    parser.add_argument("--watch", action="store_true")
    parser.add_argument("--prebuilt", action="store_true",
                        help="LML: the Lean project is already built; do not run lake update/build or patch SubVerso")
    parser.add_argument("--export-script", type=Path, default=EXPORT_SCRIPT,
                        help="LML: path of ExportLean.lean")
    parser.add_argument("--jobs", type=int, default=1,
                        help="LML: export this many entry files in parallel")
    parser.add_argument("--light-pdf", action="store_true",
                        help="LML: PDF without Lean hover annotations, hover boxes and accessibility tags "
                             "(a whole book of signatures is otherwise ~100 MB)")
    args = parser.parse_args(argv)
    documents = [ROOT / "documents" / kind for kind in DOCUMENT_KINDS] if args.all else [args.document]
    previous = None
    loaded_script = Path(__file__).stat().st_mtime_ns
    while True:
        if args.watch and Path(__file__).stat().st_mtime_ns != loaded_script:
            os.execv(sys.executable, [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]])
        current = watch_snapshot(args.project.resolve(), [p.resolve() for p in documents],
                                 args.library, args.templates, not args.prebuilt)
        failed = False
        if current != previous:
            previous = current
            refresh = args.refresh
            for document in documents:
                output = args.output / document.name if args.all and args.output else args.output
                try:
                    builder = Builder(args.project, document, output, args.modules,
                                      refresh, args.format, args.library, args.templates, args.template,
                                      args.prebuilt, args.export_script, args.light_pdf,
                                      args.jobs)
                    refresh = False
                    builder.build(args.entries, args.extract_only)
                except (subprocess.CalledProcessError, RuntimeError, ValueError, OSError) as error:
                    failed = True
                    print(f"Build failed ({document.name}): {error}", file=sys.stderr)
            args.refresh = False
        if not args.watch:
            return int(failed)
        time.sleep(0.5)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\nStopped watching.")
