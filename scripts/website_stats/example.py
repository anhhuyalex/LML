"""A small, hand-countable repository and Referee output for PR and browser checks.

Use a name outside the repository's broad scratch-file ignore patterns (not `fix*`).
"""
from __future__ import annotations

import json
import pathlib

REVISION = "1234567890abcdef1234567890abcdef12345678"
REPOSITORY = "https://github.com/anhhuyalex/LML"


def make_fixture(root: pathlib.Path):
    project, site = root / "project", root / "site"
    project.mkdir(parents=True)
    site.mkdir()
    (project / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc2\n")
    rel = "LeanMachineLearning/Example.lean"
    source = project / rel
    source.parent.mkdir()
    specs = [("A", [], "theorem A : True := by trivial"),
             ("B", ["A", "A", "B"], "theorem B : True := A"),
             ("C", ["B"], "theorem C : True := B"),
             ("D", ["A", "A"], "theorem D : A = A := rfl"),
             ("E", ["A", "Mathlib.external"], "theorem E : True := A"),
             ("namedInst", ["A"], "instance namedInst : Fact True := ⟨A⟩"),
             ("_private.Example.0.hidden", ["A"], "private theorem hidden : True := A"),
             ("instFact", ["A"], "instance : Fact True := ⟨A⟩")]
    specs += [(f"Z{i:03}", [], f"theorem Z{i:03} : True := by trivial") for i in range(65)]
    source.write_text("\n".join(text for _, _, text in specs) + "\n")
    decls, rows = [], []
    for line, (name, deps, text) in enumerate(specs, 1):
        decls.append({"name": name, "moduleName": "LeanMachineLearning.Example",
                      "modulePath": "Example",
                      "kind": "instance" if "instance" in text else "theorem", "deps": deps,
                      "typeDeps": ["A"] if name == "D" else [],
                      "source": {"relPath": rel, "line": line, "endLine": line}})
        rows.append({"name": name, "kind": "Instance" if "instance" in text else "Theorem",
                     "href": f"example/decl-{name}/"})
    # Generated companions inherit the author's source range, but are not authored declarations.
    decls.append({**decls[0], "name": "A.match_1", "deps": ["A"]})
    rows.append({"name": "A.match_1", "kind": "Theorem", "href": "example/decl-generated/"})
    shell = '''<!doctype html><html><head><base href="./"><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>Example</title>
<style>body { margin: 20px; font-family: sans-serif; } main { max-width: 950px; }</style>
</head><body><nav id="toc"><table><tr><td><a href="browse/">Browse</a></td></tr>
<tr><td><a href="sorries/#sorries">Sorries</a></td></tr>
<tr><td><a href="example/">Example</a></td></tr></table></nav>
<main><section><h1>Example</h1></section></main></body></html>'''
    (site / "index.html").write_text(shell)
    for name in ("browse", "sorries", "example"):
        (site / name).mkdir()
        (site / name / "index.html").write_text(shell.replace('href="./"', 'href="../"'))
    (site / "browse/index.html").write_text(
        shell.replace('href="./"', 'href="../"').replace("</main>",
        '<script id="browse-data" type="application/json">' +
        json.dumps({"project": "LeanMachineLearning", "rows": rows}) + '</script></main>'))
    for row in rows:
        path = site / row["href"]
        path.mkdir(parents=True)
        (path / "index.html").write_text(shell.replace('href="./"', 'href="../../"'))
    data = {"version": 16, "rootPrefix": "LeanMachineLearning", "scope": {"mode": ""},
            "decls": decls, "thinDecls": []}
    data_path = root / "referee-data.json"
    # Exercise sharing in the real format, including references from table entries to earlier entries.
    wrapped = {"version": 16, "interned": [decls, {**data, "decls": {"$i": 0}}], "data": {"$i": 1}}
    data_path.write_text(json.dumps(wrapped))
    return project, site, data_path, data


def make_dataset_fixture(root: pathlib.Path):
    """The same hand-counted declarations in the public extractor dataset protocol."""
    import struct

    project, site, _, data = make_fixture(root)
    dataset = root / "dataset"
    (dataset / "edges").mkdir(parents=True)
    (dataset / "facets").mkdir()
    ids = {decl["name"]: index for index, decl in enumerate(data["decls"])}
    nodes, sources, edges, rows = [], [], [], []
    for index, decl in enumerate(data["decls"]):
        nodes.append({"id": index, "name": decl["name"], "module": decl["moduleName"],
                      "scope": "project", "kind": decl["kind"]})
        source = decl["source"]
        sources.append({"decl": decl["name"], "path": source["relPath"],
                        "keyword": decl["kind"],
                        "start": [source["line"], 0], "end": [source["endLine"], 80]})
        edges.extend((index, ids[name]) for name in decl["deps"] if name in ids)
        rows.append([index, decl["name"], "Theorem"])
    for filename, records in [("decls.jsonl", nodes), ("facets/source.jsonl", sources)]:
        (dataset / filename).write_text("".join(json.dumps(row) + "\n" for row in records))
    (dataset / "edges/term.bin").write_bytes(b"".join(struct.pack("<ii", *edge) for edge in edges))
    meta = {"spec": "ltb-dataset/2", "toolchain": (project / "lean-toolchain").read_text().strip(),
            "library": {"root": "LeanMachineLearning", "commit": REVISION},
            "edges": [{"name": "term", "format": "i32le-pairs", "file": "edges/term.bin"}],
            "facets": [{"name": "source", "file": "facets/source.jsonl"}]}
    (dataset / "meta.json").write_text(json.dumps(meta))
    (site / "data").mkdir()
    (site / "data/decls.json").write_text(json.dumps(rows))
    (site / "data/site.json").write_text(json.dumps({"title": "Example", "root": meta["library"]["root"],
        "commit": REVISION, "toolchain": meta["toolchain"], "scope": {"mode": "full"}}))
    return project, site, dataset, data
