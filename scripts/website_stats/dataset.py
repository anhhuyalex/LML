"""Normalize extractor datasets for Stats, independently of the Lean toolchain.

Only this adapter knows the dataset protocol. Counts and the viewer consume the
same declaration/reference records as the legacy collected-JSON reader.
"""
from __future__ import annotations

import hashlib
import importlib.metadata
import json

from .reader import authored, decode, require


def input_digest(path):
    """Include names and bytes, so provenance covers the entire extracted dataset."""
    digest = hashlib.sha256()
    paths = sorted(p for p in path.rglob("*") if p.is_file()) if path.is_dir() else [path]
    for file in paths:
        if path.is_dir():
            digest.update(file.relative_to(path).as_posix().encode() + b"\0")
        with file.open("rb") as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
    return digest.hexdigest()


def load(path, project, revision):
    if path.is_file():
        data = decode(json.loads(path.read_bytes()))
        producer = {"format": "legacy-collected/16", "referee_release": "legacy format 16"}
    else:
        data, producer = load_dataset(path, project, revision)
    return data, {**producer, "input_sha256": input_digest(path)}


def load_dataset(path, project, revision):
    """Use the maintained dataset API; reject incompatible schemas, not Lean versions."""
    from evidence_core import Dataset
    from evidence_core.docs import deprecated

    meta = json.loads((path / "meta.json").read_text())
    require(meta.get("spec") == "ltb-dataset/2", "Unsupported Stats dataset schema")
    library = meta.get("library", {})
    require(isinstance(library.get("root"), str) and library["root"], "Missing library root")
    require(library.get("commit") == revision, "Dataset and source checkout revisions differ")
    require(meta.get("toolchain") == (project / "lean-toolchain").read_text().strip(),
            "Dataset and source checkout toolchains differ")
    require(any(edge["name"] == "term" for edge in meta.get("edges", [])),
            "Stats needs term edges, including proof references")
    ds = Dataset.load(path)
    by_id = {decl.id: decl for decl in ds.decls}
    sources = ds.facet("source")
    graph = ds.edges("term")
    deprecated_names = deprecated(ds)

    def source_record(decl):
        rows = sources.get(decl.name, [])
        require(len(rows) <= 1, f"Ambiguous source location: {decl.name}")
        if not rows:
            return None
        row = rows[0]
        return {"relPath": row["path"], "line": row["start"][0], "endLine": row["end"][0]}

    files = {}

    def compiler_helper(decl):
        if not decl.is_project:
            return False
        source = source_record(decl)
        if source is None:
            return True
        # An authored private declaration or instance is not a compiler helper.
        file = project / source["relPath"]
        require(file.is_file() and file.resolve().is_relative_to(project.resolve()),
                f"Missing or unsafe source: {decl.name}")
        if file not in files:
            files[file] = file.read_text().splitlines()
        lines = files[file]
        fragment = "\n".join(lines[source["line"] - 1:source["endLine"]])
        keyword = sources[decl.name][0].get("keyword")
        return keyword != "instance" and not authored(decl.name, fragment, include_private=True)

    helpers = {decl.id for decl in ds.decls if compiler_helper(decl)}

    def references(decl):
        """Expand compiler helpers only; never turn ordinary indirect uses into direct ones."""
        pending = list(graph.get(decl.id, ()))
        visited, names = set(), set()
        while pending:
            target = pending.pop()
            if target in visited:
                continue
            visited.add(target)
            require(target in by_id, f"Missing dependency node: {target}")
            if target in helpers:
                pending.extend(graph.get(target, ()))
            else:
                names.add(by_id[target].name)
        return sorted(names)

    declarations = [{"name": decl.name, "moduleName": decl.module, "kind": decl.kind,
                     "deps": references(decl), "source": source_record(decl),
                     "deprecated": decl.name in deprecated_names}
                    for decl in ds.decls if decl.is_project]
    require(declarations, "No project declarations in dataset")
    data = {"rootPrefix": library["root"], "decls": declarations,
            "_format": "ltb-dataset/2"}
    try:
        renderer_version = importlib.metadata.version("referee-site")
    except importlib.metadata.PackageNotFoundError:
        renderer_version = "external build"
    producer = {"format": meta["spec"], "extractor": meta.get("producer", {}),
                "referee_release": renderer_version,
                "evidence_core": importlib.metadata.version("evidence-core")}
    return data, producer
