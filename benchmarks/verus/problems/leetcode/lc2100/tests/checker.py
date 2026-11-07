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
    if not ints(o) or len(o) != len(set(o)):
        return False
    a, t = d["security"], d["time"]
    left, right = [0] * len(a), [0] * len(a)
    for i in range(1, len(a)):
        if a[i - 1] >= a[i]:
            left[i] = left[i - 1] + 1
    for i in range(len(a) - 2, -1, -1):
        if a[i] <= a[i + 1]:
            right[i] = right[i + 1] + 1
    return set(o) == {i for i in range(len(a)) if left[i] >= t and right[i] >= t}


CASES = [
    ({"security": [5, 3, 3, 3, 5, 6, 2], "time": 2}, [2, 3], True),
    ({"security": [5, 3, 3, 3, 5, 6, 2], "time": 2}, [3, 2], True),
    ({"security": [5, 3, 3, 3, 5, 6, 2], "time": 2}, [2, 3, 4], False),
    ({"security": [1, 2], "time": 0}, [1, 0], True),
    ({"security": [1, 2], "time": 3}, [], True),
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
