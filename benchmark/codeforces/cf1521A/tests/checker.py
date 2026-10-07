"""Standalone stdout checker for precondition-valid Codeforces stdin.
JSONL: {"input": "<stdin>", "output": "<candidate stdout>"}.
Run: python3 checker.py < cases.jsonl; or python3 checker.py --self-test.
"""
import json
import re
import sys
from math import gcd
from collections import Counter


class Tokens:
    def __init__(self, text):
        self.values = text.split()
        self.index = 0

    def word(self):
        if self.index >= len(self.values):
            raise ValueError("missing token")
        value = self.values[self.index]
        self.index += 1
        return value

    def num(self):
        token = self.word()
        if not re.fullmatch(r"[+-]?[0-9]+", token):
            raise ValueError("expected integer")
        return int(token)

    def nums(self, n):
        if not 0 <= n <= len(self.values) - self.index:
            raise ValueError("invalid count")
        return [self.num() for _ in range(n)]

    def yes(self):
        token = self.word().upper()
        if token not in ("YES", "NO"):
            raise ValueError("expected YES/NO")
        return token == "YES"

    def done(self):
        return self.index == len(self.values)


def accept(data, output):
    if not isinstance(data, str) or not isinstance(output, str):
        return False
    a, b = Tokens(data), Tokens(output)
    return judge(a, b) and a.done() and b.done()


def judge(a, b):
    for _ in range(a.num()):
        base, factor = a.num(), a.num()
        if not b.yes():
            if factor != 1:
                return False
            continue
        x, y, z = b.nums(3)
        values = (x, y, z)
        if not (len(set(values)) == 3 and all(1 <= v <= 10**18 and v % base == 0 for v in values)
                and sum(v % (base * factor) == 0 for v in values) == 1 and x + y == z):
            return False
    return True


CASES = [
    ("1\n2 3", "YES 2 4 6", True),
    ("1\n2 3", "YES 6 2 8", True),
    ("1\n2 3", "YES 2 2 4", False),
    ("1\n2 3", "NO", False),
    ("1\n2 1", "NO", True),
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
        for data, output, expected in CASES:
            if expected and (check(data, output + " extra") or check(data, "")):
                raise AssertionError("extra or missing output accepted")
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
