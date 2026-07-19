#!/usr/bin/env python3
"""Symbolic mutator for Codeforces (string-output) test cases.

Codeforces outputs are arbitrary text. We classify each output as one of:

    * single-int      "5\\n"
    * yes/no          "YES\\n" or "NO\\n" (any case)
    * num-tokens      "3 1 4 1 5\\n" or "3\\n1 2 3\\n" (only numeric tokens)
    * generic         anything else

and route to a type-aware mutation generator. All mutators preserve a single
trailing newline so the output remains a plausible-looking incorrect answer.

Per-input dedup mirrors the leetcode side: an output produced for the same
input twice is skipped. Duplicates of the original output are also skipped.

CLI:
    python3 cf_symbolic_mutator.py mutate \\
        --in benchmark/codeforces/cf1006C/tests/testcases.jsonl \\
        --out /tmp/cf_mut.jsonl --target-multiplier 10
"""
from __future__ import annotations

import argparse
import json
import random
import re
from pathlib import Path
from typing import Any, Iterator


# ---------- Output classification ----------

_INT_RE = re.compile(r"^-?\d+$")
_YESNO_RE = re.compile(r"^(?:YES|NO|Yes|No|yes|no)$")


def _strip_trailing_newlines(s: str) -> tuple[str, str]:
    """Return (body, trailing) so that body + trailing == s and trailing is whitespace-only."""
    body = s.rstrip("\n\r ")
    trailing = s[len(body):]
    return body, trailing


def classify_output(s: str) -> str:
    body, _ = _strip_trailing_newlines(s)
    if not body:
        return "generic"
    if _YESNO_RE.match(body):
        return "yes_no"
    if _INT_RE.match(body):
        return "single_int"
    tokens = body.split()
    if tokens and all(_INT_RE.match(t) for t in tokens):
        return "num_tokens"
    return "generic"


# ---------- Mutation strategies ----------

def _mut_single_int(s: str, rng: random.Random) -> Iterator[str]:
    body, trail = _strip_trailing_newlines(s)
    v = int(body)
    deltas = [1, -1, 2, -2, 5, -5, 10, -10, 100, -100]
    rng.shuffle(deltas)
    for d in deltas:
        yield f"{v + d}{trail}"
    yield f"{-v}{trail}"
    yield f"0{trail}"
    yield f"{v + 1}{trail}"
    yield f"{v - 1}{trail}"
    yield f"{v * 2}{trail}"
    yield f"{(v // 2) if v != 0 else 1}{trail}"
    while True:
        yield f"{v + rng.randint(-1000, 1000)}{trail}"


def _mut_yes_no(s: str, rng: random.Random) -> Iterator[str]:
    body, trail = _strip_trailing_newlines(s)
    if body.upper() == "YES":
        # Match the casing convention of the original.
        if body.isupper():
            yield "NO" + trail
        elif body[0].isupper():
            yield "No" + trail
        else:
            yield "no" + trail
    else:
        if body.isupper():
            yield "YES" + trail
        elif body[0].isupper():
            yield "Yes" + trail
        else:
            yield "yes" + trail
    # Also a mismatched-case variant — judges usually require an exact spelling.
    yield ("yes" if body.upper() == "NO" else "no") + trail
    yield ("YES" if body.upper() == "NO" else "NO") + trail


def _mut_num_tokens(s: str, rng: random.Random) -> Iterator[str]:
    body, trail = _strip_trailing_newlines(s)
    # Preserve line structure: list of lines, each a list of token strings.
    lines: list[list[str]] = [line.split() for line in body.split("\n")]
    flat_idx = [(li, ti) for li, line in enumerate(lines) for ti in range(len(line))]
    if not flat_idx:
        return

    def render(rows: list[list[str]]) -> str:
        return "\n".join(" ".join(row) for row in rows) + trail

    nums = [int(lines[li][ti]) for li, ti in flat_idx]

    # +1 to one token
    for _ in range(min(40, len(flat_idx))):
        i = rng.randrange(len(flat_idx))
        li, ti = flat_idx[i]
        rows = [list(r) for r in lines]
        rows[li][ti] = str(nums[i] + 1)
        yield render(rows)
    # -1 to one token
    for _ in range(min(40, len(flat_idx))):
        i = rng.randrange(len(flat_idx))
        li, ti = flat_idx[i]
        rows = [list(r) for r in lines]
        rows[li][ti] = str(nums[i] - 1)
        yield render(rows)
    # negate one token
    for _ in range(min(20, len(flat_idx))):
        i = rng.randrange(len(flat_idx))
        li, ti = flat_idx[i]
        rows = [list(r) for r in lines]
        rows[li][ti] = str(-nums[i])
        yield render(rows)
    # zero one token
    for _ in range(min(20, len(flat_idx))):
        i = rng.randrange(len(flat_idx))
        li, ti = flat_idx[i]
        rows = [list(r) for r in lines]
        rows[li][ti] = "0"
        yield render(rows)
    # all +1
    yield render([[str(int(t) + 1) for t in row] for row in lines])
    # all -1
    yield render([[str(int(t) - 1) for t in row] for row in lines])
    # negate all
    yield render([[str(-int(t)) for t in row] for row in lines])
    # swap two tokens (within full flat list)
    for _ in range(20):
        if len(flat_idx) >= 2:
            i, j = rng.sample(range(len(flat_idx)), 2)
            (li, ti), (lj, tj) = flat_idx[i], flat_idx[j]
            rows = [list(r) for r in lines]
            rows[li][ti], rows[lj][tj] = rows[lj][tj], rows[li][ti]
            yield render(rows)
    # drop the last row entirely (empty rows allowed)
    if len(lines) >= 1:
        yield render(lines[:-1]) if len(lines) > 1 else ""
    # drop the last token of the last row
    rows = [list(r) for r in lines]
    if rows and rows[-1]:
        rows[-1] = rows[-1][:-1]
        yield render(rows)
    # append a small number on the last row
    rows = [list(r) for r in lines]
    if rows:
        rows[-1] = rows[-1] + ["0"]
        yield render(rows)
    # reverse the last row
    rows = [list(r) for r in lines]
    if rows and len(rows[-1]) >= 2:
        rows[-1] = rows[-1][::-1]
        yield render(rows)
    # random tail: pick a random token, replace with a random integer near it
    while True:
        i = rng.randrange(len(flat_idx))
        li, ti = flat_idx[i]
        rows = [list(r) for r in lines]
        rows[li][ti] = str(nums[i] + rng.randint(-100, 100))
        yield render(rows)


def _mut_generic(s: str, rng: random.Random) -> Iterator[str]:
    body, trail = _strip_trailing_newlines(s)
    yield "" + trail
    if body:
        yield body[:-1] + trail
        yield body[1:] + trail
        yield body + "x" + trail
        yield "x" + body + trail
        yield body[::-1] + trail
        # swap two adjacent characters
        chars = list(body)
        for _ in range(20):
            if len(chars) >= 2:
                i = rng.randrange(len(chars) - 1)
                cs = chars[:]
                cs[i], cs[i + 1] = cs[i + 1], cs[i]
                yield "".join(cs) + trail
        # replace one character
        for _ in range(20):
            if chars:
                i = rng.randrange(len(chars))
                rep = chr(rng.randint(ord("a"), ord("z")))
                if rep != chars[i]:
                    cs = chars[:]
                    cs[i] = rep
                    yield "".join(cs) + trail
    while True:
        n = rng.randint(1, max(2, len(body) + 2))
        yield "".join(chr(rng.randint(ord("a"), ord("z"))) for _ in range(n)) + trail


_KIND_TO_GEN = {
    "single_int": _mut_single_int,
    "yes_no": _mut_yes_no,
    "num_tokens": _mut_num_tokens,
    "generic": _mut_generic,
}


def iter_mutations(value: str, rng: random.Random) -> Iterator[str]:
    kind = classify_output(value)
    gen = _KIND_TO_GEN[kind]
    return gen(value, rng)


# ---------- Public API ----------

def _canon(value: Any) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False)


def mutate_record(record: dict, rng: random.Random, max_per_record: int) -> list[dict]:
    original = record["output"]
    seen = {_canon(original)}
    out: list[dict] = []
    safety = 0
    cap = max_per_record * 50 + 100
    for cand in iter_mutations(original, rng):
        safety += 1
        if safety > cap:
            break
        k = _canon(cand)
        if k in seen:
            continue
        seen.add(k)
        out.append({"input": record["input"], "output": cand})
        if len(out) >= max_per_record:
            break
    return out


def expand_to_target(
    records: list[dict],
    target_count: int,
    rng: random.Random,
    existing: list[dict] | None = None,
) -> list[dict]:
    """Round-robin over records, asking each for one new mutation per pass."""
    out: list[dict] = list(existing or [])
    seen_per_input: dict[str, set[str]] = {}
    for r in out:
        seen_per_input.setdefault(_canon(r["input"]), set()).add(_canon(r["output"]))
    for r in records:
        seen_per_input.setdefault(_canon(r["input"]), set()).add(_canon(r["output"]))

    iters = [(r, iter_mutations(r["output"], rng)) for r in records]
    new_records: list[dict] = []
    needed = target_count - len(out)
    if needed <= 0:
        return new_records

    stalled = 0
    while needed > 0 and stalled < 3:
        progress = False
        for rec, it in iters:
            if needed <= 0:
                break
            input_key = _canon(rec["input"])
            seen = seen_per_input.setdefault(input_key, set())
            picked = None
            tries = 0
            for cand in it:
                tries += 1
                k = _canon(cand)
                if k in seen:
                    if tries > 200:
                        break
                    continue
                seen.add(k)
                picked = cand
                break
            if picked is not None:
                new_records.append({"input": rec["input"], "output": picked})
                needed -= 1
                progress = True
        if not progress:
            stalled += 1
            iters = [(r, iter_mutations(r["output"], rng)) for r, _ in iters]
        else:
            stalled = 0
    return new_records


# ---------- CLI ----------

def _read_jsonl(path: Path) -> list[dict]:
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


def _write_jsonl(path: Path, records: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w") as f:
        for r in records:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")


def cmd_mutate(args: argparse.Namespace) -> int:
    rng = random.Random(args.seed)
    records = _read_jsonl(Path(args.in_path))
    target = int(args.target_multiplier) * len(records)
    mutated = expand_to_target(records, target, rng)
    _write_jsonl(Path(args.out_path), mutated)
    print(f"original={len(records)} target={target} mutated={len(mutated)} -> {args.out_path}")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description="Symbolic mutator for Codeforces string outputs")
    sub = p.add_subparsers(dest="cmd", required=True)
    m = sub.add_parser("mutate")
    m.add_argument("--in", dest="in_path", required=True)
    m.add_argument("--out", dest="out_path", required=True)
    m.add_argument("--target-multiplier", type=int, default=10)
    m.add_argument("--seed", type=int, default=0)
    m.set_defaults(func=cmd_mutate)
    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
