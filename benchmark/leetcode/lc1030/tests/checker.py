"""Standalone output checker. Inputs must satisfy spec.rs preconditions.
Run: python3 checker.py < cases.jsonl; or python3 checker.py --self-test.
"""
import json
import sys
from collections import Counter


def integer(x):
    return type(x) is int and -(2**31) <= x < 2**31


def ints(x, length=None):
    return isinstance(x, list) and (length is None or len(x) == length) and all(map(integer, x))


def accept(d, o):
    rows, cols = d["rows"], d["cols"]
    if not isinstance(o, list) or len(o) != rows * cols or not all(ints(p, 2) for p in o):
        return False
    if len({tuple(p) for p in o}) != rows * cols:
        return False
    if any(not (0 <= r < rows and 0 <= c < cols) for r, c in o):
        return False
    distances = [abs(r - d["r_center"]) + abs(c - d["c_center"]) for r, c in o]
    return distances == sorted(distances)


CASES = [
    ({"rows": 2, "cols": 2, "r_center": 0, "c_center": 0},
     [[0, 0], [0, 1], [1, 0], [1, 1]], True),
    ({"rows": 2, "cols": 2, "r_center": 0, "c_center": 0},
     [[0, 0], [1, 0], [0, 1], [1, 1]], True),
    ({"rows": 2, "cols": 2, "r_center": 0, "c_center": 0},
     [[0, 0], [1, 1], [0, 1], [1, 0]], False),
    ({"rows": 1, "cols": 2, "r_center": 0, "c_center": 0}, [[0, 0], [0, 0]], False),
]

def check(data, output):
    """Return whether output is valid for a precondition-satisfying input."""
    try:
        return bool(accept(data, output))
    except (IndexError, KeyError, TypeError, ValueError):
        return False


def main():
    if sys.argv[1:] == ["--self-test"]:
        for i, (data, output, expected) in enumerate(CASES):
            if check(data, output) != expected:
                raise AssertionError(f"case {i}: {data!r}, {output!r}")
        for output in (None, True, 1.5, {}, "invalid"):
            if check(CASES[0][0], output):
                raise AssertionError(f"malformed output accepted: {output!r}")
        print(f"passed {len(CASES)} semantic cases and 5 malformed-output cases")
        return
    if len(sys.argv) != 1:
        raise SystemExit("usage: checker.py [--self-test] < cases.jsonl")
    errors = False
    for line in sys.stdin:
        try:
            record = json.loads(line)
            if not isinstance(record, dict) or set(record) != {"input", "output"}:
                raise ValueError("expected input/output record")
            print("accept" if check(record["input"], record["output"]) else "reject")
        except (ValueError, TypeError):
            print("error")
            errors = True
    if errors:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
