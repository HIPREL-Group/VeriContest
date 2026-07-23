"""Concrete test case: a (typed input, output) pair with provenance."""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class Case:
    input: dict | str                 # LC: {param: value}; CF: raw stdin string
    output: object                    # LC: value or {"ret":.., "<p>_after":..}; CF: raw string
    source: str = "seed"              # seed | gen | exec_mut | outmut | cross
    meta: dict = field(default_factory=dict)
