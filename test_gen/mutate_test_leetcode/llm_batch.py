#!/usr/bin/env python3
"""OpenAI Batch API pipeline for buggy LeetCode code variants.

Mirrors the request/parsing shape used by ``evaluation/run_gpt54_mini.py``:

  * endpoint: ``/v1/responses``
  * body: ``{"model": MODEL, "input": <prompt>, "temperature": 0}``
  * output: read ``response.body.output_text`` with a fallback walk over
    ``output[*].content[*].text`` for ``output_text`` items.

Subcommands:

    prepare   -> build batch_input.jsonl (one /v1/responses request per problem;
                 only problems missing ``tests/mutated_testcases.jsonl`` unless
                 ``--include-with-mutated`` is passed)
    submit    -> upload + create batch
    poll      -> wait for completion + download output
    extract   -> split each response into per-variant code files under cache/<pid>/

Variant code lives at cache/<pid>/variant_{1..5}.rs. The companion
``run_variants.py`` compiles + runs them and produces per-problem
``incorrect_llm.jsonl`` cache entries.

Environment:
    OPENAI_API_KEY        - required for submit / poll
    MUTATE_MODEL          - model name (default: gpt-5.4-mini-2026-03-17)
    MUTATE_TEMPERATURE    - default 0; set to '' to omit (gpt-5 series may reject non-default)
    MUTATE_NUM_VARIANTS   - buggy variants requested per problem (default: 5)
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
from harness_utils import LEETCODE_DIR, load_problem_files, list_leetcode_problems  # noqa: E402

MODEL = os.environ.get("MUTATE_MODEL", "gpt-5.4-2026-03-05")
# Number of buggy variants requested per problem. Five keeps the semantic
# mutation stage in line with the benchmark's documented construction.
NUM_VARIANTS = int(os.environ.get("MUTATE_NUM_VARIANTS", "5"))
# gpt-5 family rejects custom temperatures; omit the field by default for them.
# Default for other models is 0.8. Set ``MUTATE_TEMPERATURE`` explicitly to override
# either default; set it to the empty string to force-omit on any model.
_TEMP_DEFAULT = "" if MODEL.startswith("gpt-5") else "0.8"
_TEMP_RAW = os.environ.get("MUTATE_TEMPERATURE", _TEMP_DEFAULT)
INCLUDE_TEMPERATURE = _TEMP_RAW != ""
TEMPERATURE = float(_TEMP_RAW) if INCLUDE_TEMPERATURE else None


SYSTEM_INSTRUCTIONS = (
    "You are a Rust expert helping build a benchmark of *buggy* LeetCode solutions. "
    "Given a problem description and a known-correct Rust solution, produce {n} "
    "subtly broken variants. Each variant must compile under stable rustc 2021 and "
    "pass *some*, but not all, of the original test cases. Bugs should be plausible "
    "engineering mistakes (off-by-one, wrong comparator, swapped indices, missing "
    "edge case, wrong initialization, accumulator reset bug, etc.) and the {n} "
    "variants must use *different* bug categories from each other. Do not change "
    "function signatures or any helper struct definitions; only mutate function bodies."
)

USER_TEMPLATE = """\
Problem description:
---
{description}
---

Reference correct solution (code.rs):
```rust
{code}
```

Produce {n} buggy variants of this code. Each variant must:
- Be syntactically valid Rust under edition 2021.
- Keep the EXACT same `impl Solution {{ ... }}` (and any helper `impl`/`struct`)
  signatures and fn names as the reference.
- Contain a *partial* bug: it should still compile and return reasonable answers
  on many inputs while being wrong on others.
- Use a different style of bug from the other variants.

Output format (use this exactly, no extra prose, no markdown headers besides the fences):

{variant_blocks}
"""


def _variant_blocks(n: int) -> str:
    """Render the ``=== VARIANT k ===`` fenced blocks the parser expects."""
    blocks = [
        "=== VARIANT 1 ===\n```rust\n"
        "<full Rust code: any helper structs/impls and impl Solution>\n```"
    ]
    blocks += [f"=== VARIANT {i} ===\n```rust\n<...>\n```" for i in range(2, n + 1)]
    return "\n".join(blocks)


def _full_prompt(description: str, code: str, n: int = NUM_VARIANTS) -> str:
    """The /v1/responses endpoint takes a single ``input`` string, so we splice
    the system instructions and user content together with clear separators."""
    user = USER_TEMPLATE.format(
        description=description.strip(),
        code=code.strip(),
        n=n,
        variant_blocks=_variant_blocks(n),
    )
    return f"{SYSTEM_INSTRUCTIONS.format(n=n)}\n\n{user}"


def build_batch_request(problem_id: str, description: str, code: str) -> dict:
    body: dict = {
        "model": MODEL,
        "input": _full_prompt(description, code),
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
    problems = list_leetcode_problems(
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
        metadata={"description": "vcg-bench leetcode mutator: buggy variants"},
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
    """Pull the assistant text out of a /v1/responses body, mirroring run_gpt54_mini.py."""
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
    p = argparse.ArgumentParser(description="LLM buggy-variant batch pipeline")
    sub = p.add_subparsers(dest="cmd", required=True)

    pp = sub.add_parser("prepare", help="Build batch_input.jsonl")
    pp.add_argument("--problems", nargs="*", help="Restrict to these problem ids")
    pp.add_argument("--limit", type=int, default=0)
    pp.add_argument(
        "--include-with-mutated",
        action="store_true",
        help="Include problems that already have tests/mutated_testcases.jsonl "
        "(default: only problems missing that file).",
    )
    pp.set_defaults(func=cmd_prepare)

    ps = sub.add_parser("submit", help="Upload batch_input + create batch")
    ps.set_defaults(func=cmd_submit)

    pl = sub.add_parser("poll", help="Poll batch and download output when done")
    pl.add_argument("--interval", type=int, default=30)
    pl.add_argument("--once", action="store_true", help="Single poll, no loop")
    pl.set_defaults(func=cmd_poll)

    pe = sub.add_parser("extract", help="Parse responses into cache/<pid>/variant_*.rs")
    pe.add_argument("--batch-output", help="Override path to batch_output.jsonl")
    pe.set_defaults(func=cmd_extract)

    args = p.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
