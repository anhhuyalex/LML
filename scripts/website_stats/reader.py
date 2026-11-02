"""Adapter for the Referee release pinned in build.yml; no Lean extraction is needed."""
from __future__ import annotations

import collections
import json
import pathlib
import re
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit

REFEREE_COMMIT = "4f43fed3fa5a6f55ef6daf848f5a1b9dd348b0cf"
REFEREE_VERSION = "v4.34.0-rc2-7"
DATA_VERSION = 16


def require(condition, message):
    if not condition:
        raise ValueError(message)


def decode(envelope):
    require(envelope.get("version") == DATA_VERSION,
            f"Unsupported Referee data version; expected {DATA_VERSION}. "
            "Update and test the reader when changing the Referee release.")
    resolved = []

    def expand(value):
        if isinstance(value, dict):
            if set(value) == {"$i"}:
                index = value["$i"]
                require(type(index) is int and 0 <= index < len(resolved),
                        "Invalid Referee shared-data reference")
                return resolved[index]
            return {key: expand(item) for key, item in value.items()}
        if isinstance(value, list):
            return [expand(item) for item in value]
        return value

    require(isinstance(envelope.get("interned"), list) and "data" in envelope,
            "Expected Referee's collected-data envelope")
    for entry in envelope["interned"]:
        resolved.append(expand(entry))
    data = expand(envelope["data"])
    require(data.get("version") == DATA_VERSION, "Conflicting Referee data versions")
    require(data.get("scope", {}).get("mode", "") == "" and not data.get("thinDecls"),
            "Stats needs the full library, not a claims-only or single-declaration build")
    require(data.get("rootPrefix") == "LeanMachineLearning", "Expected the LML library")
    require(isinstance(data.get("decls"), list) and data["decls"], "No declarations collected")
    return data


class BrowseData(HTMLParser):
    def __init__(self, text):
        super().__init__(convert_charrefs=False)
        self.active = False
        self.parts = []
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        if tag == "script" and dict(attrs).get("id") == "browse-data":
            require(not self.parts, "Duplicate Browse data")
            self.active = True

    def handle_endtag(self, tag):
        if tag == "script":
            self.active = False

    def handle_data(self, text):
        if self.active:
            self.parts.append(text)


def local_target(site, href):
    url = urlsplit(href)
    require(not url.scheme and not url.netloc and not url.query and url.path,
            f"Expected a local documentation link: {href}")
    target = (site / unquote(url.path)).resolve()
    require(target.is_relative_to(site.resolve()), f"Link leaves the exposition: {href}")
    if target.is_dir():
        target /= "index.html"
    require(target.is_file(), f"Missing documentation page: {href}")
    if url.fragment:
        text = target.read_text()
        require(f'id="{unquote(url.fragment)}"' in text, f"Missing anchor: {href}")
    return target


def mask_comments(text):
    """Keep positions while hiding nested Lean comments and strings for name checks."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            size = 2 if text[i:i + 2] in ("/-", "-/") else 1
            if text[i:i + 2] == "/-":
                depth += 1
            elif text[i:i + 2] == "-/":
                depth -= 1
        elif string:
            size = 2 if text[i] == "\\" else 1
            if text[i] == '"':
                string = False
        elif text[i:i + 2] == "/-":
            depth, size = 1, 2
        elif text[i:i + 2] == "--":
            end = text.find("\n", i)
            size = (len(text) if end < 0 else end) - i
        elif text[i] == '"':
            string, size = True, 1
        else:
            i += 1
            continue
        for j in range(i, min(len(out), i + size)):
            if out[j] != "\n":
                out[j] = " "
        i += size
    return "".join(out)


COMMAND = re.compile(
    r"\b(theorem|lemma|def|abbrev|structure|class\s+inductive|class|inductive|axiom|opaque|"
    r"alias|instance|irreducible_def)\s+(?:\(priority\s*:=\s*[^)]*\)\s*)?"
    r"((?:«[^»]+»|[^\s({:\[⦃«])+)"
)


def authored(name, text):
    """A generated companion often shares its parent's source range; check the written name."""
    masked = mask_comments(text)
    match = COMMAND.search(masked)
    if not match:
        return False
    if re.search(r"\bprivate\b", masked[:match.start()]):
        return False
    normalized = name.replace("«", "").replace("»", "")
    if match[1] == "alias":
        # `alias ⟨leftName, rightName⟩ := iffLemma` explicitly authors two public names.
        header = masked[match.end(1):].split(":=", 1)[0].strip()
        written_names = header.removeprefix("⟨").removesuffix("⟩").split(",")
    else:
        written_names = [match[2]]
    for written in written_names:
        written = written.strip().removeprefix("_root_.").replace("«", "").replace("»", "")
        if normalized == written or normalized.endswith("." + written):
            return True
    return False


def catalog(data, site, project, repository, revision):
    require(re.fullmatch(r"[0-9a-f]{40}", revision), "Expected a full Git commit")
    require(re.fullmatch(r"https://github.com/[\w.-]+/[\w.-]+", repository),
            "Expected an HTTPS GitHub repository URL")
    parsed = BrowseData((site / "browse/index.html").read_text())
    require(parsed.parts, "Cannot find declaration links in Referee's Browse page")
    browse = json.loads("".join(parsed.parts))
    require(browse.get("project") == data["rootPrefix"], "Browse belongs to another library")
    rows = {row["name"]: row for row in browse["rows"]}
    require(len(rows) == len(browse["rows"]), "Duplicate names in Browse")
    names = [decl["name"] for decl in data["decls"]]
    require(len(set(names)) == len(names), "Duplicate collected declaration names")
    require(set(rows) == set(names), "Collected data and rendered Browse contain different declarations")
    files, included, excluded = {}, [], collections.Counter()
    for decl in sorted(data["decls"], key=lambda d: d["name"]):
        name = decl["name"]
        require(isinstance(decl.get("deps"), list) and
                all(isinstance(dep, str) for dep in decl["deps"]), f"Missing references: {name}")
        module = decl["moduleName"]
        require(module == "LeanMachineLearning" or module.startswith("LeanMachineLearning."),
                f"Unexpected external declaration: {name}")
        # Lean's derived JSON codec drops the trailing '?' from optional field names.
        source = decl.get("source")
        if name.startswith("_private.") or not source:
            excluded["private_or_no_source"] += 1
            continue
        rel = pathlib.PurePosixPath(source["relPath"])
        require(not rel.is_absolute() and ".." not in rel.parts and rel.suffix == ".lean",
                f"Invalid source path: {name}")
        path = (project / rel).resolve()
        require(path.is_relative_to(project.resolve()) and path.is_file(), f"Missing source: {rel}")
        if rel not in files:
            files[rel] = path.read_text().splitlines()
        lines = files[rel]
        start, end = source["line"], source["endLine"]
        require(type(start) is int and type(end) is int and 1 <= start <= end <= len(lines),
                f"Invalid source lines: {name}")
        fragment = "\n".join(lines[start - 1:end])
        if not authored(name, fragment):
            excluded["unnamed_or_generated"] += 1
            continue
        row = rows[name]
        local_target(site, row["href"])
        included.append({"id": name, "name": name, "module": module, "kind": row["kind"],
                         "documentation": row["href"],
                         "source": f"{repository}/blob/{revision}/{rel}#L{start}-L{end}",
                         "file": str(rel), "line": start, "end_line": end})
    require(included, "No eligible public declarations found")
    return included, dict(excluded)
