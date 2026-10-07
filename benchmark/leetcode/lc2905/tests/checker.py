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
    a, gap, difference = d["nums"], d["index_difference"], d["value_difference"]
    if not ints(o, 2):
        return False
    if o != [-1, -1]:
        i, j = o
        return (0 <= i < len(a) and 0 <= j < len(a)
                and abs(i - j) >= gap and abs(a[i] - a[j]) >= difference)
    low, high = None, None
    for j in range(gap, len(a)):
        value = a[j - gap]
        low = value if low is None else min(low, value)
        high = value if high is None else max(high, value)
        if max(a[j] - low, high - a[j]) >= difference:
            return False
    return True


CASES = [
    ({"nums": [5, 1, 4, 1], "index_difference": 2, "value_difference": 4}, [0, 3], True),
    ({"nums": [5, 1, 4, 1], "index_difference": 2, "value_difference": 4}, [3, 0], True),
    ({"nums": [5, 1, 4, 1], "index_difference": 2, "value_difference": 4}, [-1, -1], False),
    ({"nums": [2], "index_difference": 0, "value_difference": 0}, [0, 0], True),
    ({"nums": [2], "index_difference": 1, "value_difference": 0}, [-1, -1], True),
    ({"nums": [1, 1], "index_difference": 0, "value_difference": 1}, [-1, 0], False),
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
