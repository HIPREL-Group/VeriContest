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
    # Serialize CustomFunction as {"values": grid}, including unused row/column 0.
    grid, z = d["customfunction"]["values"], d["z"]
    if not isinstance(o, list) or not all(ints(p, 2) for p in o):
        return False
    expected = set()
    x, y = 1, 1000
    while x <= 1000 and y >= 1:
        value = grid[x][y]
        if value == z:
            expected.add((x, y))
            x, y = x + 1, y - 1
        elif value < z:
            x += 1
        else:
            y -= 1
    return len(o) == len(expected) and {tuple(p) for p in o} == expected


GRID = [[x + y for y in range(1001)] for x in range(1001)] if "--self-test" in sys.argv else None
CASES = [
    ({"customfunction": {"values": GRID}, "z": 4}, [[1, 3], [2, 2], [3, 1]], True),
    ({"customfunction": {"values": GRID}, "z": 4}, [[3, 1], [1, 3], [2, 2]], True),
    ({"customfunction": {"values": GRID}, "z": 4}, [[1, 3], [2, 2]], False),
    ({"customfunction": {"values": GRID}, "z": 1}, [], True),
    ({"customfunction": {"values": GRID}, "z": 4}, [[1, 3], [1, 3], [2, 2], [3, 1]], False),
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
