#!/usr/bin/env python3
"""OpenAI Batch API pipeline for buggy Codeforces code variants.

Asks the model for FIVE distinct partly-buggy variants per problem, mirroring
the request shape used by ``evaluation/run_gpt54_mini.py`` (endpoint
``/v1/responses``, single ``input`` string, no temperature for gpt-5 family).

Subcommands: prepare / submit / poll / extract.

``prepare`` only includes problems missing ``tests/mutated_testcases.jsonl``
unless you pass ``--include-with-mutated``.

Variants land at ``cache/<pid>/variant_{1..5}.rs``.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
from pathlib import Path

CACHE_DIR = Path(__file__).resolve().parent / "cache"
CACHE_DIR.mkdir(parents=True, exist_ok=True)

BATCH_INPUT = CACHE_DIR / "batch_input.jsonl"
BATCH_OUTPUT = CACHE_DIR / "batch_output.jsonl"
BATCH_ERRORS = CACHE_DIR / "batch_errors.jsonl"
BATCH_ID_FILE = CACHE_DIR / "batch_id.txt"
INPUT_FILE_ID_FILE = CACHE_DIR / "input_file_id.txt"

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cf_harness_utils import load_problem_files, list_codeforces_problems  # noqa: E402

MODEL = os.environ.get("MUTATE_MODEL", "gpt-5.4-2026-03-05")
_TEMP_DEFAULT = "" if MODEL.startswith("gpt-5") else "0.8"
_TEMP_RAW = os.environ.get("MUTATE_TEMPERATURE", _TEMP_DEFAULT)
INCLUDE_TEMPERATURE = _TEMP_RAW != ""
TEMPERATURE = float(_TEMP_RAW) if INCLUDE_TEMPERATURE else None

NUM_VARIANTS = int(os.environ.get("MUTATE_NUM_VARIANTS", "5"))


SYSTEM_INSTRUCTIONS = (
    "You are a Rust expert helping build a benchmark of *buggy* Codeforces "
    "solutions. Given a problem description and a known-correct Rust solution "
    "(which reads from stdin and writes to stdout), produce {n} subtly broken "
    "variants. Each variant must compile under stable rustc 2021 and pass "
    "*some*, but not all, of the original test cases. Bugs should be plausible "
    "engineering mistakes (off-by-one, wrong comparator, swapped indices, "
    "missing edge case, wrong initialization, accumulator reset bug, integer "
    "overflow, wrong loop bound, off-by-one in stdin parsing, etc.) and the "
    "variants must use *different* bug categories from each other. Do not "
    "change the function signature in `impl Solution` or any helper struct "
    "definitions; only mutate function bodies. Do not change the `fn main()` "
    "or stdin/stdout handling."
)

USER_TEMPLATE = """\
Problem description:
---
{description}
---

Reference correct solution (code.rs, the body of `impl Solution`):
```rust
{code}
```

Produce {n} buggy variants of this `impl Solution` block. Each variant must:
- Be syntactically valid Rust under edition 2021.
- Keep the EXACT same `impl Solution {{ ... }}` (and any helper `impl`/`struct`)
  signatures and fn names as the reference.
- Contain a *partial* bug: it should still compile and return reasonable
  answers on many inputs while being wrong on others.
- Use a different style of bug from the other variants.
- Be ONLY the `impl Solution` (and helper) block(s); do NOT include `fn main`,
  `use` statements, or stdin/stdout handling.

Output format (use this exactly, no extra prose, no markdown headers besides the fences):

{variant_blocks}
"""


def _full_prompt(description: str, code: str, n: int) -> str:
    blocks = "\n".join(
        f"=== VARIANT {i} ===\n```rust\n<full impl Solution block (and helper structs/impls if needed)>\n```"
        for i in range(1, n + 1)
    )
    user = USER_TEMPLATE.format(
        description=description.strip(),
        code=code.strip(),
        n=n,
        variant_blocks=blocks,
    )
    return f"{SYSTEM_INSTRUCTIONS.format(n=n)}\n\n{user}"


def build_batch_request(problem_id: str, description: str, code: str) -> dict:
    body: dict = {
        "model": MODEL,
        "input": _full_prompt(description, code, NUM_VARIANTS),
    }
    if INCLUDE_TEMPERATURE:
        body["temperature"] = TEMPERATURE
    return {
        "custom_id": problem_id,
        "method": "POST",
        "url": "/v1/responses",
        "body": body,
    }


# ---------- Subcommands ----------

def cmd_prepare(args: argparse.Namespace) -> int:
    problems = list_codeforces_problems(
        only_missing_mutated=not args.include_with_mutated,
    )
    if args.problems:
        wanted = set(args.problems)
        problems = [p for p in problems if p.name in wanted]
    if args.limit:
        problems = problems[: args.limit]
    BATCH_INPUT.parent.mkdir(parents=True, exist_ok=True)
    written = 0
    with open(BATCH_INPUT, "w") as f:
        for pdir in problems:
            try:
                desc, code, _ = load_problem_files(pdir)
            except FileNotFoundError as e:
                print(f"[skip] {pdir.name}: {e}", file=sys.stderr)
                continue
            req = build_batch_request(pdir.name, desc, code)
            f.write(json.dumps(req, ensure_ascii=False) + "\n")
            written += 1
    print(f"Wrote {written} requests -> {BATCH_INPUT}")
    print(
        f"  Model: {MODEL}, variants/problem: {NUM_VARIANTS}, "
        f"temperature: {'(omitted)' if not INCLUDE_TEMPERATURE else TEMPERATURE}"
    )
    return 0


def cmd_submit(args: argparse.Namespace) -> int:
    from openai import OpenAI

    if not BATCH_INPUT.exists():
        print(f"missing {BATCH_INPUT} (run prepare first)", file=sys.stderr)
        return 1
    client = OpenAI()
    with open(BATCH_INPUT, "rb") as f:
        file_obj = client.files.create(file=f, purpose="batch")
    print(f"file id: {file_obj.id}")
    INPUT_FILE_ID_FILE.write_text(file_obj.id + "\n")
    batch = client.batches.create(
        input_file_id=file_obj.id,
        endpoint="/v1/responses",
        completion_window="24h",
        metadata={"description": "vcg-bench codeforces mutator: buggy variants"},
    )
    print(f"batch id: {batch.id} status: {batch.status}")
    BATCH_ID_FILE.write_text(batch.id + "\n")
    return 0


def cmd_poll(args: argparse.Namespace) -> int:
    from openai import OpenAI

    if not BATCH_ID_FILE.exists():
        print(f"missing {BATCH_ID_FILE} (run submit first)", file=sys.stderr)
        return 1
    batch_id = BATCH_ID_FILE.read_text().strip()
    client = OpenAI()
    while True:
        batch = client.batches.retrieve(batch_id)
        rc = getattr(batch, "request_counts", None)
        if rc is not None:
            print(
                f"[{time.strftime('%H:%M:%S')}] {batch.status} "
                f"({rc.completed + rc.failed}/{rc.total}, ok={rc.completed} fail={rc.failed})"
            )
        else:
            print(f"[{time.strftime('%H:%M:%S')}] {batch.status}")
        if batch.status in ("completed", "failed", "expired", "cancelled"):
            break
        if args.once:
            return 0
        time.sleep(args.interval)
    if batch.output_file_id:
        content = client.files.content(batch.output_file_id)
        BATCH_OUTPUT.write_bytes(content.read())
        print(f"wrote {BATCH_OUTPUT}")
    if getattr(batch, "error_file_id", None):
        content = client.files.content(batch.error_file_id)
        BATCH_ERRORS.write_bytes(content.read())
        print(f"wrote {BATCH_ERRORS}")
    return 0 if batch.status == "completed" else 2


_VARIANT_RE = re.compile(
    r"===\s*VARIANT\s*(\d+)\s*===\s*```(?:rust)?\s*\n(.*?)```",
    re.DOTALL | re.IGNORECASE,
)


def parse_variants(text: str) -> dict[int, str]:
    out: dict[int, str] = {}
    for m in _VARIANT_RE.finditer(text):
        idx = int(m.group(1))
        code = m.group(2).strip()
        if code and idx not in out:
            out[idx] = code
    return out


def _extract_text(response_body: dict) -> str:
    text = response_body.get("output_text") or ""
    if text:
        return text
    for item in response_body.get("output", []) or []:
        if item.get("type") != "message":
            continue
        for content in item.get("content", []) or []:
            if content.get("type") == "output_text":
                t = content.get("text") or ""
                if t:
                    return t
    return ""


def cmd_extract(args: argparse.Namespace) -> int:
    src = Path(args.batch_output) if args.batch_output else BATCH_OUTPUT
    if not src.exists():
        print(f"missing {src}", file=sys.stderr)
        return 1
    n_problems = 0
    n_variants = 0
    n_skip = 0
    with open(src) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            obj = json.loads(line)
            pid = obj.get("custom_id")
            if obj.get("error"):
                n_skip += 1
                continue
            response = obj.get("response", {}) or {}
            body = response.get("body", {}) or {}
            content = _extract_text(body)
            if not pid or not content:
                n_skip += 1
                continue
            variants = parse_variants(content)
            if not variants:
                n_skip += 1
                continue
            pdir = CACHE_DIR / pid
            pdir.mkdir(parents=True, exist_ok=True)
            (pdir / "raw_response.txt").write_text(content)
            for idx, code in variants.items():
                (pdir / f"variant_{idx}.rs").write_text(code + "\n")
                n_variants += 1
            n_problems += 1
    print(f"extracted: problems={n_problems} variants={n_variants} skipped={n_skip}")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description="LLM buggy-variant batch pipeline (Codeforces)")
    sub = p.add_subparsers(dest="cmd", required=True)

    pp = sub.add_parser("prepare")
    pp.add_argument("--problems", nargs="*")
    pp.add_argument("--limit", type=int, default=0)
    pp.add_argument(
        "--include-with-mutated",
        action="store_true",
        help="Include problems that already have tests/mutated_testcases.jsonl "
        "(default: only problems missing that file).",
    )
    pp.set_defaults(func=cmd_prepare)

    ps = sub.add_parser("submit")
    ps.set_defaults(func=cmd_submit)

    pl = sub.add_parser("poll")
    pl.add_argument("--interval", type=int, default=30)
    pl.add_argument("--once", action="store_true")
    pl.set_defaults(func=cmd_poll)

    pe = sub.add_parser("extract")
    pe.add_argument("--batch-output")
    pe.set_defaults(func=cmd_extract)

    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
