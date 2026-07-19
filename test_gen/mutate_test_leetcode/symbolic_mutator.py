#!/usr/bin/env python3
"""Symbolic mutator for LeetCode test outputs.

Generates incorrect outputs by perturbing the correct one with a small,
deterministic-but-randomized library of mutators. Outputs are deduped so we
never emit a "mutation" that equals the original.

CLI:
    python symbolic_mutator.py mutate \
        --in benchmark/leetcode/lc1/tests/testcases.jsonl \
        --out benchmark/leetcode/lc1/tests/mutated_symbolic.jsonl \
        --target-multiplier 10

Programmatic:
    from symbolic_mutator import mutate_record, expand_to_target
"""
from __future__ import annotations

import argparse
import json
import random
from pathlib import Path
from typing import Any, Iterator


# ---------- Type detection ----------

def output_kind(value: Any) -> str:
    if isinstance(value, bool):
        return "bool"
    if isinstance(value, int):
        return "int"
    if isinstance(value, float):
        return "float"
    if isinstance(value, str):
        return "str"
    if isinstance(value, list):
        if not value:
            return "list_empty"
        first = value[0]
        if isinstance(first, bool):
            return "list_bool"
        if isinstance(first, int):
            return "list_int"
        if isinstance(first, float):
            return "list_float"
        if isinstance(first, str):
            return "list_str"
        if isinstance(first, list):
            if not first:
                return "list_list_empty"
            inner = first[0]
            if isinstance(inner, bool):
                return "list_list_bool"
            if isinstance(inner, int):
                return "list_list_int"
            if isinstance(inner, str):
                return "list_list_str"
        return "list_unknown"
    return "unknown"


# ---------- Per-type mutators ----------

def _mut_int(v: int, rng: random.Random) -> Iterator[int]:
    deltas = [1, -1, 2, -2, 5, -5, 10, -10, 100, -100]
    rng.shuffle(deltas)
    for d in deltas:
        yield v + d
    yield -v
    yield 0
    yield v + 1
    yield v - 1
    yield v * 2
    yield v // 2 if v != 0 else 1
    yield v + rng.randint(1, 50)
    yield v - rng.randint(1, 50)
    # Big random
    while True:
        yield v + rng.randint(-1000, 1000)


def _mut_float(v: float, rng: random.Random) -> Iterator[float]:
    deltas = [0.1, -0.1, 1.0, -1.0, 0.5, -0.5]
    rng.shuffle(deltas)
    for d in deltas:
        yield round(v + d, 5)
    yield -v
    yield 0.0
    while True:
        yield round(v + rng.uniform(-10.0, 10.0), 5)


def _mut_bool(v: bool, rng: random.Random) -> Iterator[bool]:
    yield not v


def _mut_str(v: str, rng: random.Random) -> Iterator[str]:
    yield ""
    yield v + "x"
    yield "x" + v
    if v:
        yield v[:-1]
        yield v[1:]
        yield v[::-1]
        # Swap two adjacent characters
        chars = list(v)
        for _ in range(20):
            if len(chars) >= 2:
                i = rng.randrange(len(chars) - 1)
                chars2 = chars[:]
                chars2[i], chars2[i + 1] = chars2[i + 1], chars2[i]
                yield "".join(chars2)
        # Replace one char with a different letter
        for _ in range(20):
            if chars:
                i = rng.randrange(len(chars))
                replacement = chr(rng.randint(ord("a"), ord("z")))
                if replacement != chars[i]:
                    chars2 = chars[:]
                    chars2[i] = replacement
                    yield "".join(chars2)
    while True:
        # Random alpha string of len in [0, max(1, len+2)]
        n = rng.randint(0, max(1, len(v) + 2))
        yield "".join(chr(rng.randint(ord("a"), ord("z"))) for _ in range(n))


def _mut_list_int(v: list[int], rng: random.Random) -> Iterator[list[int]]:
    if v:
        # +1 to one element
        for _ in range(min(20, max(1, len(v)))):
            i = rng.randrange(len(v))
            out = list(v)
            out[i] = out[i] + 1
            yield out
        # -1 to one element
        for _ in range(min(20, max(1, len(v)))):
            i = rng.randrange(len(v))
            out = list(v)
            out[i] = out[i] - 1
            yield out
        # Swap two elements
        for _ in range(20):
            if len(v) >= 2:
                i, j = rng.sample(range(len(v)), 2)
                out = list(v)
                out[i], out[j] = out[j], out[i]
                yield out
        # Drop last
        yield v[:-1]
        # Drop first
        yield v[1:]
        # Append element
        yield list(v) + [v[-1] + 1]
        yield list(v) + [0]
        # Reverse
        yield list(reversed(v))
        # Sorted ascending
        yield sorted(v)
        # Sorted descending
        yield sorted(v, reverse=True)
        # Replace element with 0
        for _ in range(10):
            i = rng.randrange(len(v))
            out = list(v)
            out[i] = 0
            yield out
        # All elements +1
        yield [x + 1 for x in v]
        # All elements -1
        yield [x - 1 for x in v]
        # Negate
        yield [-x for x in v]
    yield []
    # Random length
    while True:
        n = rng.randint(1, max(1, len(v) + 2))
        out = [rng.randint(-50, 50) for _ in range(n)]
        yield out


def _mut_list_bool(v: list[bool], rng: random.Random) -> Iterator[list[bool]]:
    if v:
        for i in range(len(v)):
            out = list(v)
            out[i] = not out[i]
            yield out
        yield [not x for x in v]
        yield v[:-1]
        yield v[1:]
        yield list(reversed(v))
    yield []
    while True:
        n = rng.randint(1, max(1, len(v) + 2))
        yield [rng.choice([True, False]) for _ in range(n)]


def _mut_list_str(v: list[str], rng: random.Random) -> Iterator[list[str]]:
    if v:
        # Mutate one string element
        for _ in range(20):
            i = rng.randrange(len(v))
            inner = v[i]
            mutated = ""
            if inner:
                mutated = inner[:-1] if rng.random() < 0.5 else inner + "x"
            else:
                mutated = "x"
            out = list(v)
            out[i] = mutated
            yield out
        yield v[:-1]
        yield v[1:]
        yield list(reversed(v))
        if len(v) >= 2:
            for _ in range(10):
                i, j = rng.sample(range(len(v)), 2)
                out = list(v)
                out[i], out[j] = out[j], out[i]
                yield out
    yield []
    while True:
        n = rng.randint(1, max(1, len(v) + 2))
        yield [
            "".join(chr(rng.randint(ord("a"), ord("z"))) for _ in range(rng.randint(0, 4)))
            for _ in range(n)
        ]


def _mut_list_list_int(v: list[list[int]], rng: random.Random) -> Iterator[list[list[int]]]:
    if v:
        for _ in range(30):
            i = rng.randrange(len(v))
            row = v[i]
            if not row:
                continue
            j = rng.randrange(len(row))
            out = [list(r) for r in v]
            out[i][j] = out[i][j] + rng.choice([1, -1, 2, -2])
            yield out
        if len(v) >= 2:
            for _ in range(10):
                i, j = rng.sample(range(len(v)), 2)
                out = [list(r) for r in v]
                out[i], out[j] = out[j], out[i]
                yield out
        yield v[:-1]
        yield v[1:]
        yield list(reversed(v))
    yield []
    while True:
        n = rng.randint(1, max(1, len(v) + 2))
        m = rng.randint(1, 4)
        yield [[rng.randint(-20, 20) for _ in range(m)] for _ in range(n)]


def _mut_generic_list(v: list, rng: random.Random) -> Iterator[list]:
    """Fallback for lists whose element type we don't specialize on."""
    if v:
        yield v[:-1]
        yield v[1:]
        yield list(reversed(v))
    yield []


# ---------- Mutation dispatcher ----------

_KIND_TO_GEN = {
    "int": _mut_int,
    "float": _mut_float,
    "bool": _mut_bool,
    "str": _mut_str,
    "list_int": _mut_list_int,
    "list_bool": _mut_list_bool,
    "list_float": _mut_list_int,  # close enough for our coverage
    "list_str": _mut_list_str,
    "list_list_int": _mut_list_list_int,
    "list_list_bool": _mut_generic_list,
    "list_list_str": _mut_generic_list,
    "list_empty": lambda v, rng: iter([[0], [1], [0, 0]]),
    "list_list_empty": lambda v, rng: iter([[[0]], [[]]]),
    "list_unknown": _mut_generic_list,
}


def iter_mutations(value: Any, rng: random.Random) -> Iterator[Any]:
    kind = output_kind(value)
    gen = _KIND_TO_GEN.get(kind)
    if gen is None:
        return iter([])
    return gen(value, rng)


def mutate_record(record: dict, rng: random.Random, max_per_record: int) -> list[dict]:
    """Produce up to ``max_per_record`` distinct mutations of ``record['output']``.

    Each returned dict is ``{"input": ..., "output": <mutated>}`` (no extra fields,
    matching the format of the original testcases.jsonl).
    """
    original = record.get("output")
    seen = {_canon(original)}
    out: list[dict] = []
    gen = iter_mutations(original, rng)
    safety = 0
    safety_cap = max_per_record * 50 + 100
    for candidate in gen:
        safety += 1
        if safety > safety_cap:
            break
        key = _canon(candidate)
        if key in seen:
            continue
        seen.add(key)
        new_rec = {"input": record["input"], "output": candidate}
        out.append(new_rec)
        if len(out) >= max_per_record:
            break
    return out


def _canon(value: Any) -> str:
    """Canonical key for dedup; use sorted-keys JSON."""
    return json.dumps(value, sort_keys=True, ensure_ascii=False)


def expand_to_target(
    records: list[dict],
    target_count: int,
    rng: random.Random,
    existing: list[dict] | None = None,
) -> list[dict]:
    """Return a list of mutated records whose total count + len(existing) >= target_count.

    Cycles round-robin over original records, asking each for one new mutation per pass,
    so that mutations stay balanced across inputs even when target_count is small.
    """
    out: list[dict] = list(existing or [])
    seen_per_input: dict[str, set[str]] = {}
    for r in out:
        key = _canon(r["input"])
        seen_per_input.setdefault(key, set()).add(_canon(r["output"]))
    for r in records:
        key = _canon(r["input"])
        seen_per_input.setdefault(key, set()).add(_canon(r["output"]))

    iters = []
    for r in records:
        iters.append((r, iter_mutations(r["output"], rng)))

    new_records: list[dict] = []
    needed = target_count - len(out)
    if needed <= 0:
        return new_records

    stalled_passes = 0
    while needed > 0 and stalled_passes < 3:
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
            stalled_passes += 1
            # Restart iterators with a fresh stream so the while-True tails restart.
            iters = [(r, iter_mutations(r["output"], rng)) for r, _ in iters]
        else:
            stalled_passes = 0

    return new_records


# ---------- CLI ----------

def _read_jsonl(path: Path) -> list[dict]:
    out = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            out.append(json.loads(line))
    return out


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
    print(
        f"original={len(records)} target={target} mutated={len(mutated)} "
        f"-> {args.out_path}"
    )
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description="Symbolic output mutator for testcases.jsonl")
    sub = p.add_subparsers(dest="cmd", required=True)
    m = sub.add_parser("mutate", help="Mutate outputs to N x")
    m.add_argument("--in", dest="in_path", required=True, help="Path to testcases.jsonl")
    m.add_argument("--out", dest="out_path", required=True, help="Output mutated jsonl path")
    m.add_argument("--target-multiplier", type=int, default=10)
    m.add_argument("--seed", type=int, default=0)
    m.set_defaults(func=cmd_mutate)
    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
