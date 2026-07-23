"""Validity gates for candidate inputs, in cost order: schema/range (pure),
execution (built driver), requires (Verus pre-gate), dedup. An unavailable
tool means status "skip", never a silent pass."""
from __future__ import annotations

from dataclasses import dataclass

from spec_testing.common.specmodel import SpecModel
from spec_testing.common.values import spec_type, coerce_ok


@dataclass
class GateOutcome:
    ok: bool
    status: str          # "pass" | "fail" | "skip"
    reason: str = ""


def gate_schema(input_obj: dict, model: SpecModel) -> GateOutcome:
    """Gate 1: every param value is renderable for its (stripped) spec type."""
    for p in model.params:
        if p.name not in input_obj:
            return GateOutcome(False, "fail", f"missing param {p.name}")
        st = spec_type(p.rust_type)
        if not coerce_ok(input_obj[p.name], st):
            return GateOutcome(False, "fail", f"type/range: {p.name}")
    return GateOutcome(True, "pass")


class Deduper:
    """Gate 4: structural dedup across retained inputs."""

    def __init__(self) -> None:
        self._seen: set[str] = set()

    def check(self, input_obj) -> GateOutcome:
        import json
        key = json.dumps(input_obj, sort_keys=True)
        if key in self._seen:
            return GateOutcome(False, "fail", "duplicate")
        self._seen.add(key)
        return GateOutcome(True, "pass")
