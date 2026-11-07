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
    if not isinstance(o, dict) or set(o) != {"return", "nums"}:
        return False
    k, a = o["return"], o["nums"]
    counts = Counter(d["nums"])
    expected = [v for v in sorted(counts) for _ in range(min(2, counts[v]))]
    return (integer(k) and ints(a, len(d["nums"])) and k == len(expected)
            and a[:k] == expected)


CASES = [
    ({"nums": [1, 1, 1, 2]}, {"return": 3, "nums": [1, 1, 2, 9]}, True),
    ({"nums": [1, 1, 1, 2]}, {"return": 3, "nums": [1, 1, 2, -5]}, True),
    ({"nums": [1, 1, 1, 2]}, {"return": 4, "nums": [1, 1, 1, 2]}, False),
    ({"nums": [1, 1, 1, 2]}, {"return": 3, "nums": [1, 2, 1, 0]}, False),
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
