"""Each metric declares its explanation, calculation, and shared display style.

Reuse follows lean-code-reuse's M1: distinct users, union of type and value references.
Our population is explicitly the public authored LML declarations in the catalog.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


@dataclass(frozen=True)
class Metric:
    id: str
    title: str
    explanation: str
    x_label: str
    display: str
    compute: Callable
    subject: str = "declaration"
    method: str = "compiled_references"
    notes: str = ""


def reuse(catalog, data):
    users = {decl["id"]: set() for decl in catalog}
    for decl in data["decls"]:
        caller = decl["name"]
        if caller in users:
            for target in set(decl["deps"]):
                if target in users and target != caller:
                    users[target].add(caller)
    return {name: len(callers) for name, callers in users.items()}


METRICS = (Metric(
    id="reuse", title="How often are declarations reused?",
    explanation=("If three different declarations use a lemma, its count is three. "
                 "Click a bar to see the declarations with that many uses."),
    notes=("Statements, proofs, and definition bodies all count. Several uses inside one "
                 "declaration count once. Uses through another public declaration do not add to the count. "
                 "Private helpers, unnamed instances, and declarations Lean creates automatically "
                 "are excluded from both sides. Zero means no use in this measured group; "
                 "it does not mean the declaration is unnecessary. Lean's automatic helper code "
                 "is followed to recover references in the author's declaration."),
    x_label="Number of other declarations using it", display="histogram", compute=reuse,
),)


def results(catalog, data):
    return [{"id": metric.id, "title": metric.title, "explanation": metric.explanation,
             "x_label": metric.x_label, "y_label": "Number of declarations",
             "display": metric.display, "subject": metric.subject, "method": metric.method,
             "notes": metric.notes,
             "values": metric.compute(catalog, data)} for metric in METRICS]
