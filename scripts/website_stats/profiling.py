"""Join a Beam timing report to the exact declaration catalog it measured."""
from __future__ import annotations

import hashlib
import json
import statistics

from .reader import require

PROFILE_METRIC = "declaration-time"
TRIALS = 3
UNMEASURED = {
    "no_command", "shared_command", "source_error", "beam_error", "rejected", "timeout",
    "budget", "pilot",
}


def catalog_fingerprint(declarations):
    fields = ("id", "module", "kind", "file", "line", "end_line")
    rows = sorted(tuple(row[field] for field in fields) for row in declarations)
    return hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest()


def report_header(build, declarations):
    return {
        "schema_version": 1, "repository": build["repository"], "revision": build["revision"],
        "lean": build["lean"], "catalog_sha256": catalog_fingerprint(declarations),
    }


def validate_report(report, build, declarations):
    require(isinstance(report, dict), "Expected a Beam timing report")
    for name, expected in report_header(build, declarations).items():
        require(type(report.get(name)) is type(expected) and report[name] == expected,
                f"Beam timing report does not match the site ({name})")
    require(report.get("mode") == "full", "Only full profiling runs can be published")
    for field in ("beam", "beam_revision", "runner"):
        require(isinstance(report.get(field), str) and report[field].strip(),
                f"Missing timing report provenance ({field})")
    readings = report.get("readings")
    require(isinstance(readings, dict) and set(readings) == {d["id"] for d in declarations},
            "Beam timing report must account for every declaration")
    for key, result in readings.items():
        if isinstance(result, str):
            require(result in UNMEASURED - {"pilot"}, f"Unknown unmeasured reason for {key}")
        else:
            require(isinstance(result, list) and len(result) == TRIALS and
                    all(type(v) is int and 0 <= v <= 2**53 - 1 for v in result),
                    f"Invalid Beam trial readings for {key}")


def timing_metric(report, declarations):
    # Beam reports tenths of a millisecond. Keep integers for exact histogram boundaries.
    readings = report["readings"] if report else {}
    values = {key: statistics.median(trials) for key, trials in readings.items()
              if isinstance(trials, list)}
    ordered = sorted(values.values())
    n = len(ordered)
    return {
        "id": PROFILE_METRIC, "title": "Declaration processing time",
        "explanation": ("How long Lean took to process each declaration with its imports loaded. "
                        "Choose a bar to see the declarations in that range."),
        "notes": ("We timed each whole declaration three times and used the middle reading. "
                  "Timing depends on the machine and includes the overhead of profiling. "
                  "Nine out of ten measured declarations took at most the 90th-percentile time. "
                  "Declarations without three successful trials are left out of the chart."),
        "x_label": "Time to process a declaration", "y_label": "Number of declarations",
        "display": "histogram", "subject": "declaration", "method": "beam_reelaboration",
        "values": values, "eligible": len(declarations), "unit": "tenth_ms",
        "summary": {"median": statistics.median(ordered), "p90": ordered[(9 * n + 9) // 10 - 1]}
        if n else None,
    }
