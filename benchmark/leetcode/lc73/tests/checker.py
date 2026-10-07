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
    a = d["matrix"]
    if not isinstance(o, dict) or set(o) != {"matrix"}:
        return False
    b = o["matrix"]
    m, n = len(a), len(a[0])
    if not isinstance(b, list) or len(b) != m or not all(ints(row, n) for row in b):
        return False
    rows = {i for i in range(m) if 0 in a[i]}
    cols = {j for j in range(n) if any(a[i][j] == 0 for i in range(m))}
    return all(b[i][j] == (0 if i in rows or j in cols else a[i][j])
               for i in range(m) for j in range(n))


CASES = [
    ({"matrix": [[1, 0], [3, 4]]}, {"matrix": [[0, 0], [3, 0]]}, True),
    ({"matrix": [[1, 0], [3, 4]]}, {"matrix": [[0, 0], [0, 0]]}, False),
    ({"matrix": [[1, 2]]}, {"matrix": [[1, 2]]}, True),
    ({"matrix": [[1, 2]]}, {"matrix": [[1], [2]]}, False),
    ({"matrix": [[0]]}, {"matrix": [[False]]}, False),
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
