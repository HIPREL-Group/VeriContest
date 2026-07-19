#!/usr/bin/env python3
"""
Batch test-case generation pipeline for VCG-Bench.

Uses the OpenAI Batch API to generate ~200 test cases per problem
(combined random + adversarial) for all benchmark problems, producing
plain Rust generators that are compiled and validated locally.

Validated batch output is written as ``tests/gen_adv.rs`` (and
``tests/gen_adv_bin``), matching the adversarial-generator naming used
for hand-written problems (e.g. ``leetcode/lc1/tests/gen_adv.rs``).
Those hand-written files are **Verus-verified**; batch-produced
``gen_adv.rs`` is **not** — it is checked only by ``rustc``, running
the binary, and the reference oracle (``include!`` ``code.rs``). Do not run ``validate`` on a
problem id that already has a Verus ``gen_adv.rs`` you want to keep,
unless you back it up first.

Subcommands
-----------
    prepare   -- discover problems, build prompts, write gen/batch_input.jsonl
    submit    -- upload JSONL + create batch, save batch ID
    poll      -- poll batch status, download results when done
    validate    -- parse responses, compile gen_adv.rs, run, compute outputs
    materialize -- existing gen_adv.rs -> test inputs; code.rs (include! oracle) -> outputs -> adv_testcase.json
    run-async   -- generate Verus-verified gen_adv.rs with async API + repair loop
    retry       -- collect failures, build retry batch with error feedback
    status      -- show per-problem status summary

Usage
-----
    python test_gen/gen_testcases.py prepare [--kind leetcode|codeforces|both]
    python test_gen/gen_testcases.py submit
    python test_gen/gen_testcases.py poll
    python test_gen/gen_testcases.py validate [--workers 8]
    python test_gen/gen_testcases.py materialize [--kind both] [--limit 0]
    python test_gen/gen_testcases.py materialize [--problem cf1A lc1] [--seed 42]
    python test_gen/gen_testcases.py run-async [--problem lc1 lc9] [--max-retries 8]

``materialize`` uses ``--timeout`` (default 30s) for ``gen_adv_bin`` and
``--oracle-timeout`` (default 600s) for the reference oracle (ground truth).
``validate`` uses ``--timeout`` for the generator and ``--oracle-timeout`` (default
600s) for the oracle. ``run-async`` uses ``--timeout`` (default 30s) for the
generator and ``--oracle-timeout`` (default 600s) for the oracle after a
successful Verus verify. Log lines like ``reference oracle timed out (90s)``
mean that run used a lower ``--oracle-timeout`` (or older single-timeout
behavior).

When you **already** have ``tests/gen_adv.rs`` for every problem and only need
``tests/adv_testcase.json`` (inputs from ``gen_adv_bin``, outputs from ``code.rs``
via the reference oracle), use **materialize** — not ``run-async``. Pass
``--limit 0`` to process the full benchmark set (no cap).

Failures from ``materialize`` / ``validate`` / ``run-async`` testcase steps are
appended as JSON lines to ``test_gen/gen_pipeline_errors.jsonl``; set
``GEN_PIPELINE_ERROR_LOG`` to use a different path.

    python test_gen/gen_testcases.py retry
    python test_gen/gen_testcases.py status
"""

from __future__ import annotations

import argparse
import asyncio
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
BENCH_ROOT = REPO_ROOT / "benchmark"
# Checked after VERUS env and before ``PATH`` (see ``find_verus_binary``).
DEFAULT_VERUS_BINARY = REPO_ROOT / "verus" / "verus"
GEN_DIR = REPO_ROOT / "test_gen" / "gen"

# Subprocess timeout (seconds) for running ``reference_oracle_bin`` (``include!`` ``code.rs``).
DEFAULT_REFERENCE_ORACLE_TIMEOUT_S = 600

# Append-only JSONL of failures from validate / materialize / run-async testcase steps.
_DEFAULT_PIPELINE_ERROR_LOG = REPO_ROOT / "test_gen" / "gen_pipeline_errors.jsonl"
_pipeline_error_lock = threading.Lock()

_TEST_GEN_DIR = Path(__file__).resolve().parent
if str(_TEST_GEN_DIR) not in sys.path:
    sys.path.insert(0, str(_TEST_GEN_DIR))
from build_harness import build_reference_oracle_bin  # noqa: E402


def append_pipeline_error(
    command: str,
    problem_id: str,
    stage: str,
    detail: str,
    *,
    extra: dict[str, Any] | None = None,
) -> None:
    """Append one JSON line for later triage (thread-safe). Set ``GEN_PIPELINE_ERROR_LOG`` or default under ``test_gen/``."""
    path = Path(os.environ.get("GEN_PIPELINE_ERROR_LOG", str(_DEFAULT_PIPELINE_ERROR_LOG)))
    rec: dict[str, Any] = {
        "ts": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "command": command,
        "problem_id": problem_id,
        "stage": stage,
        "detail": (detail or "")[:32000],
    }
    if extra:
        rec["extra"] = extra
    line = json.dumps(rec, ensure_ascii=False) + "\n"
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with _pipeline_error_lock:
            with open(path, "a", encoding="utf-8") as f:
                f.write(line)
    except OSError as e:
        print(f"[append_pipeline_error] could not write {path}: {e}", file=sys.stderr)


# LLM batch pipeline writes here (plain Rust + rustc; not Verus-verified).
GEN_ADV_RS_NAME = "gen_adv.rs"
GEN_ADV_BIN_NAME = "gen_adv_bin"

MODEL = os.environ.get("GEN_MODEL", "claude-opus-4-7")
MAX_TOKENS = int(os.environ.get("GEN_MAX_TOKENS", "8000"))
TEMPERATURE = float(os.environ.get("GEN_TEMPERATURE", "0.7"))

MAX_ERROR_CHARS = int(os.environ.get("GEN_MAX_ERROR_CHARS", "8000"))
EXAMPLE_GEN_ADV_PATH = BENCH_ROOT / "leetcode" / "lc1" / "tests" / "gen_adv.rs"

@dataclass
class Signature:
    method: str
    args: list[tuple[str, str]]
    ret: str

    def arg_names_csv(self) -> str:
        return ", ".join(n for n, _ in self.args)

    def json_fields(self) -> list[str]:
        return [n for n, _ in self.args]


@dataclass
class ProblemInfo:
    problem_id: str          # e.g. "lc1", "cf1A"
    problem_dir: Path
    spec_rs: str
    description_md: str
    code_rs: str
    signature: Signature


@dataclass
class ProblemStatus:
    problem_id: str
    stage: str = "discovered"   # discovered / prompted / generated / compiled / ran / validated / output_computed / done / error
    error: str = ""
    attempt: int = 0
    test_count: int = 0


# ---------------------------------------------------------------------------
# Problem discovery
# ---------------------------------------------------------------------------

def load_ignore_set(kind_root: Path) -> set[str]:
    ignore_file = kind_root / ".benchmark-ignore"
    if not ignore_file.exists():
        return set()
    return {line.strip() for line in ignore_file.read_text().splitlines() if line.strip()}


def _find_balanced_parens(text: str, start: int) -> int | None:
    """Return index past the closing ')' that matches the '(' at `start`."""
    if start >= len(text) or text[start] != '(':
        return None
    depth = 0
    for i in range(start, len(text)):
        if text[i] == '(':
            depth += 1
        elif text[i] == ')':
            depth -= 1
            if depth == 0:
                return i + 1
    return None


def _find_return_and_body(text: str, after_paren: int) -> tuple[str, int]:
    """After the closing ')' of args, find optional '-> RET' and the '{'."""
    rest = text[after_paren:]
    m = re.match(r'\s*(->\s*(?P<ret>.+?))?\s*\{', rest, re.DOTALL)
    if not m:
        return "()", after_paren
    ret = (m.group("ret") or "()").strip()
    return ret, after_paren + m.end()


def parse_signature(code_rs: str) -> Signature:
    # Match `pub fn NAME(` or `fn NAME(` -- then use balanced-paren scanner
    # to handle nested parens in tuple types like Vec<(usize, usize)>.
    m = re.search(r'(?:pub\s+)?fn\s+(\w+)\s*\(', code_rs, re.DOTALL)
    if not m:
        raise ValueError("no `fn` signature found in code.rs")
    name = m.group(1)
    paren_start = m.end() - 1  # position of '('
    paren_end = _find_balanced_parens(code_rs, paren_start)
    if paren_end is None:
        raise ValueError("unbalanced parentheses in signature")
    args_raw = code_rs[paren_start + 1 : paren_end - 1].strip()
    ret, _ = _find_return_and_body(code_rs, paren_end)

    args: list[tuple[str, str]] = []
    if args_raw:
        depth_angle = 0
        depth_paren = 0
        cur = ""
        parts: list[str] = []
        for ch in args_raw:
            if ch == "<":
                depth_angle += 1
            elif ch == ">":
                depth_angle -= 1
            elif ch == "(":
                depth_paren += 1
            elif ch == ")":
                depth_paren -= 1
            if ch == "," and depth_angle == 0 and depth_paren == 0:
                parts.append(cur)
                cur = ""
            else:
                cur += ch
        if cur.strip():
            parts.append(cur)
        for p in parts:
            p = p.strip()
            # Skip &self / &mut self
            if p in ("&self", "&mut self", "self"):
                continue
            if ":" not in p:
                raise ValueError(f"cannot parse arg fragment: {p!r}")
            n, t = p.split(":", 1)
            n = n.strip()
            if n.startswith("mut "):
                n = n[4:]
            args.append((n.strip(), t.strip()))
    return Signature(method=name, args=args, ret=ret)


def iter_problems(kind: str) -> list[Path]:
    kinds: list[Path] = []
    if kind in ("leetcode", "both"):
        kinds.append(BENCH_ROOT / "leetcode")
    if kind in ("codeforces", "both"):
        kinds.append(BENCH_ROOT / "codeforces")
    out: list[Path] = []
    for root in kinds:
        if not root.exists():
            continue
        ignore = load_ignore_set(root)
        for p in sorted(root.iterdir()):
            if not p.is_dir():
                continue
            if p.name in ignore:
                continue
            required = ["spec.rs", "code_spec.rs", "description.md", "code.rs"]
            if all((p / f).exists() for f in required):
                out.append(p)
    return out


def load_problem(problem_dir: Path) -> ProblemInfo:
    pid = problem_dir.name
    spec_rs = (problem_dir / "spec.rs").read_text()
    description_md = (problem_dir / "description.md").read_text()
    code_rs = (problem_dir / "code.rs").read_text()
    sig = parse_signature(code_rs)
    return ProblemInfo(
        problem_id=pid,
        problem_dir=problem_dir,
        spec_rs=spec_rs,
        description_md=description_md,
        code_rs=code_rs,
        signature=sig,
    )


# ---------------------------------------------------------------------------
# Prompt construction
# ---------------------------------------------------------------------------

SYSTEM_PROMPT = """\
You are an expert Rust programmer and software testing engineer.
Your task is to write a standalone Rust test-input generator program.
The program must compile with `rustc` directly (no Cargo, no external crates).
Output ONLY a single ```rust code block containing the complete program.
Do not include any explanation outside the code block."""

def build_user_prompt(info: ProblemInfo) -> str:
    sig = info.signature
    args_str = ", ".join(f"{n}: {t}" for n, t in sig.args)
    ret_str = f" -> {sig.ret}" if sig.ret != "()" else ""
    plain_sig = f"fn {sig.method}({args_str}){ret_str}"

    json_obj_fields = []
    for n, t in sig.args:
        json_obj_fields.append(f'"{n}": <value>')
    json_template = "{" + ", ".join(json_obj_fields) + "}"

    return f"""\
== PROBLEM DESCRIPTION ==
{info.description_md.strip()}

== VERUS SPECIFICATION (spec.rs) ==
{info.spec_rs.strip()}

== FUNCTION SIGNATURE (plain Rust) ==
{plain_sig}

== TASK ==
Write a standalone Rust program (compiled with `rustc`, no external crates)
that generates approximately 200 test inputs for the function above.

Follow these steps IN ORDER inside the program:

Step 1 — Constraint analysis:
  Read the `requires` clause in the Verus specification carefully.
  Identify every input constraint (value ranges, length bounds,
  structural properties like sortedness or uniqueness, existential
  requirements like "there exists a pair summing to target", etc.).

Step 2 — Failure-mode analysis:
  Think about ~10 potential mistakes an LLM might make when
  implementing this function. Focus on problem-specific bugs, not
  generic issues. Examples: off-by-one on indices, mishandling
  duplicates, integer overflow on intermediate sums, wrong comparison
  direction for sorted output, etc.

Step 3 — Generator implementation:
  Write a `fn main()` that:
  a) Accepts a single command-line argument: an integer seed.
  b) Uses a simple LCG PRNG seeded from that argument (no `rand` crate).
  c) Generates ~100 random test cases with diverse sizes and values,
     all satisfying every constraint from the `requires` clause.
  d) Generates ~100 adversarial test cases specifically targeting the
     failure modes from Step 2 (boundary values, minimal/maximal sizes,
     corner cases for this specific problem).
  e) Prints one JSON object per line to stdout in this exact format:
       {json_template}
     (input fields only — no "output" field, no wrapper object)

CRITICAL constraints on the generator:
- Every generated input MUST satisfy ALL constraints in the `requires`
  clause. If a constraint is existential (e.g. "exists i,j such that ..."),
  the generator must construct inputs that provably satisfy it.
- Use only the Rust standard library. No external crates.
- The program must compile with `rustc` directly.
- Print nothing to stdout except the JSON lines (no headers, no comments).
- Handle string inputs by printing them as JSON strings.
- Handle Vec/array inputs by printing them as JSON arrays.
- Handle nested Vec<Vec<T>> by printing as nested JSON arrays.
"""


# ---------------------------------------------------------------------------
# Verus-verified generation prompts
# ---------------------------------------------------------------------------

VERUS_SYSTEM_PROMPT = """\
You are an expert Rust and Verus engineer.
Write a Verus-verified test-input generator that compiles with `verus --compile`.

Structure:
1. `use vstd::prelude::*;` at the top.
2. `verus! { }` block with a `pub fn generate_test_case(...)` that has
   `requires`/`ensures` clauses formally proving every output satisfies
   the problem specification's preconditions.
3. Plain Rust code (no Verus syntax, no external crates) outside the
   `verus!` block for: a simple LCG PRNG, adversarial test-case logic,
   and `fn main()` that prints JSON lines to stdout.

Output ONLY a single ```rust code block. No explanation outside the block."""


def build_verus_user_prompt(info: ProblemInfo, example_code: str) -> str:
    sig = info.signature
    args_str = ", ".join(f"{n}: {t}" for n, t in sig.args)
    ret_str = f" -> {sig.ret}" if sig.ret != "()" else ""
    plain_sig = f"fn {sig.method}({args_str}){ret_str}"

    json_fields = [f'"{n}": <value>' for n, _ in sig.args]
    json_template = "{" + ", ".join(json_fields) + "}"

    prompt = f"""\
== PROBLEM DESCRIPTION ==
{info.description_md.strip()}

== VERUS SPECIFICATION (spec.rs) ==
{info.spec_rs.strip()}

== FUNCTION SIGNATURE ==
{plain_sig}

== TASK ==
Write a Verus-verified test-input generator. It must compile and verify
with `verus --compile`.

The program has two parts:

**Part 1 -- Verified (inside `verus! {{ }}`):**

Write `pub fn generate_test_case(...)` that:
- Takes *decomposed* parameters (key values, indices, filler arrays, etc.)
  from which a valid test input can be assembled.
- Has `requires` constraining these parameters.
- Has `ensures` proving the returned value satisfies EVERY constraint in
  the spec's `requires` clause above.
- Implements a verified body assembling the result.
- You may add spec helper functions if needed for the proof.

**Part 2 -- Unverified (outside `verus! {{ }}`):**

Plain Rust (no Verus syntax, no external crates):
a) LCG PRNG struct seeded from a CLI argument.
b) ~10 adversarial modes targeting likely implementation bugs.
c) `fn main()` that generates ~200 test cases (random + adversarial),
   calls `generate_test_case` for each, and prints one JSON per line:
     {json_template}

CRITICAL:
- `ensures` of `generate_test_case` must match/imply `requires` of
  the target function in the spec. This is what makes every generated
  test case a provably valid input.
- `use vstd::prelude::*;` at the top.
- No crates besides vstd. Unverified part uses only std.
- Stdout must contain only JSON lines (no headers, no comments).
- Use `int` for spec-level integers, concrete types (i32, usize) for exec.
- Add loop invariants for every while/for loop inside verus!.
- Use `assert` statements to help the verifier with intermediate proof steps.
"""
    if example_code:
        prompt += f"""
== REFERENCE EXAMPLE (a verified generator for a different problem) ==
```rust
{example_code.strip()}
```
"""
    return prompt


# ---------------------------------------------------------------------------
# Verus helper functions
# ---------------------------------------------------------------------------

def find_verus_binary(explicit: str | None = None) -> str | None:
    if explicit:
        p = Path(explicit)
        if not p.is_absolute():
            p = (REPO_ROOT / explicit.lstrip("./")).resolve()
        else:
            p = p.resolve()
        if p.is_file():
            return str(p)
    env_verus = os.environ.get("VERUS")
    if env_verus:
        p = Path(env_verus)
        if not p.is_absolute():
            p = (REPO_ROOT / env_verus.lstrip("./")).resolve()
        else:
            p = p.resolve()
        if p.is_file():
            return str(p)
    if DEFAULT_VERUS_BINARY.is_file():
        return str(DEFAULT_VERUS_BINARY.resolve())
    found = shutil.which("verus")
    if found:
        return found
    return None


def compile_gen_adv_binary(
    tests_dir: Path,
    verus_bin: str | None,
    *,
    rustc_timeout: int = 60,
    verus_timeout: int = 600,
    force: bool = False,
) -> tuple[Path | None, str]:
    """
    Produce ``tests/gen_adv_bin`` from ``tests/gen_adv.rs``.

    Tries ``rustc`` first (for plain-Rust batch generators). If that fails and
    ``verus_bin`` is set, runs ``verus --compile`` (for Verus ``verus!`` generators).
    """
    gen_rs = tests_dir / GEN_ADV_RS_NAME
    gen_bin = tests_dir / GEN_ADV_BIN_NAME
    default_bin = tests_dir / gen_rs.stem
    if not gen_rs.exists():
        return None, f"missing {gen_rs}"
    if gen_bin.exists() and not force:
        return gen_bin, ""
    if force:
        for p in (gen_bin, default_bin):
            try:
                if p.exists():
                    p.unlink()
            except OSError:
                pass
    result = subprocess.run(
        ["rustc", str(gen_rs), "-o", str(gen_bin), "-O"],
        capture_output=True,
        text=True,
        timeout=rustc_timeout,
    )
    if result.returncode == 0:
        return gen_bin, ""
    rustc_err = (result.stderr or result.stdout or "rustc failed").strip()
    if not verus_bin:
        return None, rustc_err[:2000]
    status, detail = verify_with_verus(gen_rs, verus_bin, verus_timeout)
    if status != "verified":
        return None, (detail or "verus failed")[:2000]
    if default_bin.exists() and not gen_bin.exists():
        default_bin.rename(gen_bin)
    if gen_bin.exists():
        return gen_bin, ""
    return None, "verus succeeded but gen_adv_bin not found (expected ./gen_adv or ./gen_adv_bin)"


def verify_with_verus(target: Path, verus_bin: str,
                      timeout: int = 600) -> tuple[str, str]:
    try:
        result = subprocess.run(
            [verus_bin, "--compile", "--no-cheating", str(target.resolve())],
            cwd=target.parent,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return "verify_error", f"verus timed out ({timeout}s)"
    if result.returncode == 0:
        return "verified", ""
    err = (result.stderr or result.stdout or "").strip()
    return "verify_error", trim_middle(err, MAX_ERROR_CHARS)


def trim_middle(text: str, max_chars: int) -> str:
    if len(text) <= max_chars:
        return text
    keep_head = max_chars // 2
    keep_tail = max_chars - keep_head - 64
    omitted = len(text) - keep_head - keep_tail
    return text[:keep_head] + f"\n\n... [truncated {omitted} chars] ...\n\n" + text[-keep_tail:]


def build_verus_followup_prompt(error_text: str) -> str:
    return f"""\
The previous code failed Verus verification/compilation.

== VERUS ERROR ==
```text
{trim_middle(error_text, MAX_ERROR_CHARS)}
```

Please fix the code and return the complete replacement as a single ```rust code block.
Common issues:
- Missing or insufficient loop invariants (every while/for needs invariants)
- Missing proof assertions (use `assert` to guide the verifier)
- Type mismatches: spec uses `int`/`nat`, exec uses `i32`/`usize`/`i64`
- Quantifier trigger issues (use `#[trigger]` annotations)
- Arithmetic overflow: ensure intermediate values stay in range
- `decreases` clause missing for loops
- Proof blocks `proof {{ ... }}` needed for complex assertions
"""


async def async_chat_completion(client: Any, messages: list[dict[str, str]]) -> str:
    system_text = ""
    user_messages = []
    for m in messages:
        if m["role"] == "system":
            system_text = m["content"]
        else:
            user_messages.append(m)
    kwargs: dict[str, Any] = {
        "model": MODEL,
        "messages": user_messages,
        "max_tokens": MAX_TOKENS,
    }
    if system_text:
        kwargs["system"] = system_text
    response = await client.messages.create(**kwargs)
    texts = [block.text for block in response.content if hasattr(block, "text")]
    return "\n".join(texts) if texts else ""


# ---------------------------------------------------------------------------
# Batch JSONL assembly
# ---------------------------------------------------------------------------

def build_batch_request(info: ProblemInfo) -> dict:
    return {
        "custom_id": info.problem_id,
        "method": "POST",
        "url": "/v1/chat/completions",
        "body": {
            "model": MODEL,
            "messages": [
                {"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": build_user_prompt(info)},
            ],
            "temperature": TEMPERATURE,
            "max_completion_tokens": MAX_TOKENS,
        },
    }


# ---------------------------------------------------------------------------
# Status tracking
# ---------------------------------------------------------------------------

def status_path() -> Path:
    return GEN_DIR / "status.json"


def load_status() -> dict[str, ProblemStatus]:
    sp = status_path()
    if not sp.exists():
        return {}
    data = json.loads(sp.read_text())
    out: dict[str, ProblemStatus] = {}
    for pid, d in data.items():
        out[pid] = ProblemStatus(**d)
    return out


def save_status(statuses: dict[str, ProblemStatus]) -> None:
    GEN_DIR.mkdir(parents=True, exist_ok=True)
    data = {pid: asdict(s) for pid, s in statuses.items()}
    status_path().write_text(json.dumps(data, indent=2) + "\n")


def update_status(statuses: dict[str, ProblemStatus], pid: str,
                  stage: str, error: str = "", **kwargs: Any) -> None:
    if pid not in statuses:
        statuses[pid] = ProblemStatus(problem_id=pid)
    statuses[pid].stage = stage
    statuses[pid].error = error
    for k, v in kwargs.items():
        setattr(statuses[pid], k, v)


# ---------------------------------------------------------------------------
# Response parsing
# ---------------------------------------------------------------------------

RUST_BLOCK_RE = re.compile(r"```rust\s*\n(.*?)```", re.DOTALL)


def extract_rust_code(response_text: str) -> str | None:
    m = RUST_BLOCK_RE.search(response_text)
    if m:
        return m.group(1).strip()
    return None


# ---------------------------------------------------------------------------
# Subcommand: prepare
# ---------------------------------------------------------------------------

def cmd_prepare(args: argparse.Namespace) -> int:
    problems = iter_problems(args.kind)
    if args.problem:
        wanted = set(args.problem)
        problems = [p for p in problems if p.name in wanted]
    if args.limit:
        problems = problems[:args.limit]
    if not problems:
        print("No problems found.", file=sys.stderr)
        return 1

    statuses = load_status()
    GEN_DIR.mkdir(parents=True, exist_ok=True)
    jsonl_path = GEN_DIR / "batch_input.jsonl"

    loaded = 0
    errors = 0
    with open(jsonl_path, "w") as f:
        for pdir in problems:
            try:
                info = load_problem(pdir)
            except Exception as e:
                print(f"[error] {pdir.name}: {e}", file=sys.stderr)
                update_status(statuses, pdir.name, "error", str(e))
                errors += 1
                continue
            req = build_batch_request(info)
            f.write(json.dumps(req) + "\n")
            update_status(statuses, info.problem_id, "prompted")
            loaded += 1

    save_status(statuses)
    print(f"Prepared {loaded} problems -> {jsonl_path}")
    if errors:
        print(f"  {errors} errors (see status.json)")
    print(f"  Model: {MODEL}, max_completion_tokens: {MAX_TOKENS}, temperature: {TEMPERATURE}")
    return 0


# ---------------------------------------------------------------------------
# Subcommand: submit
# ---------------------------------------------------------------------------

def cmd_submit(args: argparse.Namespace) -> int:
    try:
        from openai import OpenAI
    except ImportError:
        print("openai package not installed. Run: pip install openai", file=sys.stderr)
        return 1

    client = OpenAI()
    jsonl_path = args.input if args.input else GEN_DIR / "batch_input.jsonl"
    if not jsonl_path.exists():
        print(f"{jsonl_path} not found. Run `prepare` first.", file=sys.stderr)
        return 1

    print(f"Uploading {jsonl_path} ...")
    with open(jsonl_path, "rb") as f:
        file_obj = client.files.create(file=f, purpose="batch")
    print(f"  File ID: {file_obj.id}")

    print("Creating batch ...")
    batch = client.batches.create(
        input_file_id=file_obj.id,
        endpoint="/v1/chat/completions",
        completion_window="24h",
        metadata={"description": "vcg-bench test case generation"},
    )
    print(f"  Batch ID: {batch.id}")
    print(f"  Status:   {batch.status}")

    id_path = GEN_DIR / "batch_id.txt"
    id_path.write_text(batch.id + "\n")
    print(f"  Saved to {id_path}")

    file_id_path = GEN_DIR / "input_file_id.txt"
    file_id_path.write_text(file_obj.id + "\n")

    return 0


# ---------------------------------------------------------------------------
# Subcommand: poll
# ---------------------------------------------------------------------------

def cmd_poll(args: argparse.Namespace) -> int:
    try:
        from openai import OpenAI
    except ImportError:
        print("openai package not installed.", file=sys.stderr)
        return 1

    id_path = GEN_DIR / "batch_id.txt"
    if not id_path.exists():
        print(f"{id_path} not found. Run `submit` first.", file=sys.stderr)
        return 1
    batch_id = id_path.read_text().strip()

    client = OpenAI()
    interval = args.interval

    while True:
        batch = client.batches.retrieve(batch_id)
        ts = time.strftime("%H:%M:%S")
        completed = batch.request_counts.completed if batch.request_counts else "?"
        total = batch.request_counts.total if batch.request_counts else "?"
        failed = batch.request_counts.failed if batch.request_counts else "?"
        print(f"[{ts}] status={batch.status}  completed={completed}/{total}  failed={failed}")

        if batch.status in ("completed", "failed", "expired", "cancelled"):
            break
        time.sleep(interval)

    if batch.status != "completed":
        print(f"Batch ended with status: {batch.status}", file=sys.stderr)
        if batch.errors:
            for err in batch.errors.data:
                print(f"  {err.code}: {err.message}", file=sys.stderr)
        return 1

    output_file_id = batch.output_file_id
    if not output_file_id:
        print("No output file ID in completed batch.", file=sys.stderr)
        return 1

    print(f"Downloading output file {output_file_id} ...")
    content = client.files.content(output_file_id)
    out_path = GEN_DIR / "batch_output.jsonl"
    out_path.write_bytes(content.read())
    print(f"  Saved to {out_path}")

    if batch.error_file_id:
        err_content = client.files.content(batch.error_file_id)
        err_path = GEN_DIR / "batch_errors.jsonl"
        err_path.write_bytes(err_content.read())
        print(f"  Errors saved to {err_path}")

    return 0


# ---------------------------------------------------------------------------
# Subcommand: validate
# ---------------------------------------------------------------------------

def validate_one(
    problem_dir: Path,
    response_text: str,
    statuses: dict[str, ProblemStatus],
    generator_timeout: int,
    oracle_timeout: int,
) -> None:
    pid = problem_dir.name
    tests_dir = problem_dir / "tests"
    tests_dir.mkdir(parents=True, exist_ok=True)

    # 1. Extract Rust code
    code = extract_rust_code(response_text)
    if not code:
        msg = "no ```rust block in response"
        update_status(statuses, pid, "error", msg)
        append_pipeline_error("validate", pid, "no_rust_block", msg)
        return
    gen_rs = tests_dir / GEN_ADV_RS_NAME
    gen_rs.write_text(code)
    update_status(statuses, pid, "generated")

    # 2. Compile (plain Rust from batch; ``force`` because gen_adv.rs was just overwritten)
    gen_bin, compile_err = compile_gen_adv_binary(tests_dir, None, force=True)
    if not gen_bin:
        msg = f"compile failed:\n{compile_err}"
        update_status(statuses, pid, "error", msg)
        append_pipeline_error("validate", pid, "compile_gen_adv", msg)
        return
    update_status(statuses, pid, "compiled")

    # 3. Run generator
    try:
        result = subprocess.run(
            [str(gen_bin), "42"],
            capture_output=True, text=True, timeout=generator_timeout,
        )
    except subprocess.TimeoutExpired:
        msg = f"generator timed out ({generator_timeout}s)"
        update_status(statuses, pid, "error", msg)
        append_pipeline_error("validate", pid, "generator_timeout", msg)
        return
    if result.returncode != 0:
        err = (result.stderr or "")[:2000]
        msg = f"generator crashed:\n{err}"
        update_status(statuses, pid, "error", msg)
        append_pipeline_error("validate", pid, "generator_crash", msg)
        return

    raw_lines = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    cases: list[dict] = []
    parse_errors = 0
    for line in raw_lines:
        try:
            obj = json.loads(line)
            if isinstance(obj, dict):
                cases.append(obj)
            else:
                parse_errors += 1
        except json.JSONDecodeError:
            parse_errors += 1

    if not cases:
        msg = (
            f"generator produced 0 valid JSON cases ({len(raw_lines)} lines, {parse_errors} parse errors)"
        )
        update_status(statuses, pid, "error", msg)
        append_pipeline_error("validate", pid, "generator_no_json", msg)
        return
    update_status(statuses, pid, "ran", test_count=len(cases))

    # 4. Compute outputs using ``code.rs`` pulled in via ``include!(\"../code.rs\")`` (reference oracle)
    oracle_bin, oerr = build_reference_oracle_bin(problem_dir)
    if not oracle_bin:
        msg = f"reference oracle: {oerr}"
        update_status(statuses, pid, "error", msg)
        append_pipeline_error("validate", pid, "reference_oracle_build", msg)
        return
    input_jsonl = "\n".join(json.dumps(c) for c in cases) + "\n"
    try:
        result = subprocess.run(
            [str(oracle_bin)],
            input=input_jsonl, capture_output=True, text=True,
            timeout=oracle_timeout,
        )
    except subprocess.TimeoutExpired:
        msg = f"reference oracle timed out ({oracle_timeout}s)"
        update_status(statuses, pid, "error", msg)
        append_pipeline_error("validate", pid, "reference_oracle_timeout", msg)
        return
    if result.returncode != 0:
        err = (result.stderr or "")[:8000]
        msg = f"reference oracle failed:\n{err}"
        update_status(statuses, pid, "error", msg)
        first_line = input_jsonl.split("\n", 1)[0] if input_jsonl.strip() else ""
        append_pipeline_error(
            "validate",
            pid,
            "reference_oracle_run",
            msg,
            extra={"returncode": result.returncode, "first_input_jsonl_line": first_line[:4000]},
        )
        return

    output_cases: list[dict] = []
    for line in result.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
            output_cases.append(obj)
        except json.JSONDecodeError:
            pass

    if output_cases:
        cases = output_cases
    update_status(statuses, pid, "output_computed", test_count=len(cases))

    # 5. Deduplicate
    seen: set[str] = set()
    unique: list[dict] = []
    for c in cases:
        key = json.dumps(c, sort_keys=True)
        if key not in seen:
            seen.add(key)
            unique.append(c)
    cases = unique

    # 6. Write adv_testcase.json
    tc_path = tests_dir / "adv_testcase.json"
    with open(tc_path, "w") as f:
        f.write("[\n")
        for i, c in enumerate(cases):
            comma = "," if i < len(cases) - 1 else ""
            f.write("  " + json.dumps(c, separators=(",", ": ")) + comma + "\n")
        f.write("]\n")

    update_status(statuses, pid, "done", test_count=len(cases))


def find_problem_dir(pid: str) -> Path | None:
    for kind_dir in (BENCH_ROOT / "leetcode", BENCH_ROOT / "codeforces"):
        pdir = kind_dir / pid
        if pdir.exists():
            return pdir
    return None


def cmd_validate(args: argparse.Namespace) -> int:
    out_path = GEN_DIR / "batch_output.jsonl"
    if not out_path.exists():
        print(f"{out_path} not found. Run `poll` first.", file=sys.stderr)
        return 1

    # Parse batch output
    responses: dict[str, str] = {}
    for line in out_path.read_text().splitlines():
        if not line.strip():
            continue
        obj = json.loads(line)
        pid = obj["custom_id"]
        body = obj.get("response", {}).get("body", {})
        choices = body.get("choices", [])
        if choices:
            text = choices[0].get("message", {}).get("content", "")
            responses[pid] = text
        else:
            responses[pid] = ""

    statuses = load_status()
    log_path = Path(os.environ.get("GEN_PIPELINE_ERROR_LOG", str(_DEFAULT_PIPELINE_ERROR_LOG)))
    print(f"Failures append to: {log_path} (GEN_PIPELINE_ERROR_LOG)", flush=True)

    items = list(responses.items())
    total_v = len(items)
    done = 0
    errors = 0
    for i, (pid, text) in enumerate(items, 1):
        print(f"[progress {i}/{total_v}] {pid} ...", flush=True)
        problem_dir = find_problem_dir(pid)
        if not problem_dir:
            print(f"[error] {pid}: problem directory not found", file=sys.stderr)
            update_status(statuses, pid, "error", "problem directory not found")
            errors += 1
            continue

        if not text:
            update_status(statuses, pid, "error", "empty response from API")
            errors += 1
            continue

        try:
            validate_one(
                problem_dir,
                text,
                statuses,
                args.timeout,
                args.oracle_timeout,
            )
        except Exception as e:
            update_status(statuses, pid, "error", f"exception: {e}")
            errors += 1
            continue

        if statuses[pid].stage == "error":
            errors += 1
        else:
            done += 1

    save_status(statuses)
    print(f"\nValidation complete: {done} succeeded, {errors} errors out of {len(responses)}")
    return 0


# ---------------------------------------------------------------------------
# Subcommand: materialize (gen_adv.rs + include! code.rs oracle -> adv_testcase.json)
# ---------------------------------------------------------------------------

def cmd_materialize(args: argparse.Namespace) -> int:
    """Compile ``gen_adv.rs``, run it with ``--seed``, pipe JSON through a ``code.rs`` oracle (``include!``), write ``adv_testcase.json``."""
    verus_bin = find_verus_binary(args.verus)
    problems = iter_problems(args.kind)
    if args.problem:
        wanted = set(args.problem)
        problems = [p for p in problems if p.name in wanted]
    if args.limit is not None and args.limit > 0:
        problems = problems[: args.limit]
    if not problems:
        print("No problems found.", file=sys.stderr)
        return 1

    if not verus_bin:
        print(
            "(no verus binary: Verus generators need ``verus`` on PATH, "
            f"``VERUS``, ``--verus``, or a file at ``{DEFAULT_VERUS_BINARY}`` if rustc fails)",
            file=sys.stderr,
        )

    total_m = len(problems)
    log_path = Path(os.environ.get("GEN_PIPELINE_ERROR_LOG", str(_DEFAULT_PIPELINE_ERROR_LOG)))
    print(f"materialize: {total_m} problem(s) selected", flush=True)
    print(f"Failures append to: {log_path} (override with GEN_PIPELINE_ERROR_LOG)", flush=True)
    t0 = time.monotonic()
    ok = 0
    failures = 0
    for i, p in enumerate(problems, 1):
        pid = p.name
        print(f"[progress {i}/{total_m}] {pid} ...", flush=True)
        outcome = "?"
        tests_dir = p / "tests"
        if not (tests_dir / GEN_ADV_RS_NAME).exists():
            print(f"[skip] {pid}: missing tests/{GEN_ADV_RS_NAME}", file=sys.stderr)
            failures += 1
            outcome = "skip_no_gen_adv"
            append_pipeline_error(
                "materialize",
                pid,
                outcome,
                f"missing {tests_dir / GEN_ADV_RS_NAME}",
            )
        else:
            gen_bin, cerr = compile_gen_adv_binary(
                tests_dir,
                verus_bin,
                force=args.force_compile,
                rustc_timeout=args.rustc_timeout,
                verus_timeout=args.verus_timeout,
            )
            if not gen_bin:
                print(f"[error] {pid}: compile gen_adv: {cerr}", file=sys.stderr)
                failures += 1
                outcome = "compile_error"
                append_pipeline_error("materialize", pid, outcome, cerr[:32000])
            else:
                statuses: dict[str, ProblemStatus] = {}
                stage = collect_test_cases(
                    pid,
                    gen_bin,
                    tests_dir,
                    args.timeout,
                    statuses,
                    seed=str(args.seed),
                    force_oracle=args.force_oracle,
                    error_source="materialize",
                    oracle_timeout=args.oracle_timeout,
                )
                outcome = stage
                if stage == "done":
                    ok += 1
                else:
                    detail = statuses[pid].error if pid in statuses else ""
                    print(f"[error] {pid}: stage={stage} {detail[:800]}", file=sys.stderr)
                    failures += 1
        print(
            f"[progress {i}/{total_m}] {pid} -> {outcome} ({time.monotonic() - t0:.1f}s elapsed)",
            flush=True,
        )

    print(
        f"\nmaterialize: {ok} ok, {failures} failed/skipped (of {total_m} selected) "
        f"in {time.monotonic() - t0:.1f}s",
        flush=True,
    )
    return 0 if failures == 0 else 1


# ---------------------------------------------------------------------------
# Subcommand: run-async (Verus-verified generation with repair loop)
# ---------------------------------------------------------------------------

def collect_test_cases(
    pid: str,
    gen_bin: Path,
    tests_dir: Path,
    timeout: int,
    statuses: dict[str, ProblemStatus],
    seed: str = "42",
    *,
    force_oracle: bool = False,
    error_source: str = "materialize",
    oracle_timeout: int | None = None,
) -> str:
    if not gen_bin.exists():
        update_status(statuses, pid, "verified")
        print(f"[{pid}] binary not found after verification; marked as verified only")
        return "verified"

    try:
        result = subprocess.run(
            [str(gen_bin), str(seed)],
            capture_output=True, text=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        msg = f"generator timed out ({timeout}s)"
        update_status(statuses, pid, "error", msg)
        append_pipeline_error(error_source, pid, "generator_timeout", msg)
        return "error"
    if result.returncode != 0:
        err = (result.stderr or "")[:2000]
        msg = f"generator crashed:\n{err}"
        update_status(statuses, pid, "error", msg)
        append_pipeline_error(error_source, pid, "generator_crash", msg)
        return "error"

    cases: list[dict] = []
    stdout = result.stdout.strip()
    try:
        parsed = json.loads(stdout)
        if isinstance(parsed, list):
            cases = [c for c in parsed if isinstance(c, dict)]
    except json.JSONDecodeError:
        pass

    if not cases:
        for line in result.stdout.splitlines():
            line = line.strip().rstrip(",")
            if not line or line in ("[", "]"):
                continue
            try:
                obj = json.loads(line)
                if isinstance(obj, dict):
                    cases.append(obj)
            except json.JSONDecodeError:
                pass

    if not cases:
        msg = "generator produced 0 valid JSON cases"
        update_status(statuses, pid, "error", msg)
        append_pipeline_error(error_source, pid, "generator_no_json", msg)
        return "error"

    # ``gen_adv`` may emit fully materialized cases (e.g. stdin/stdout CF format with ``output``).
    if cases and all(isinstance(c, dict) and "output" in c for c in cases):
        seen: set[str] = set()
        unique: list[dict] = []
        for c in cases:
            key = json.dumps(c, sort_keys=True)
            if key not in seen:
                seen.add(key)
                unique.append(c)
        cases = unique
        tc_path = tests_dir / "adv_testcase.json"
        with open(tc_path, "w") as f:
            f.write("[\n")
            for i, c in enumerate(cases):
                comma = "," if i < len(cases) - 1 else ""
                f.write("  " + json.dumps(c, separators=(",", ": ")) + comma + "\n")
            f.write("]\n")
        update_status(statuses, pid, "done", test_count=len(cases))
        print(f"[{pid}] done (pre-filled outputs): {len(cases)} test cases written")
        return "done"

    # Compute outputs via ``code.rs`` (``tests/reference_oracle.rs`` uses ``include!(\"../code.rs\")``)
    problem_dir = tests_dir.parent
    oracle_bin, oerr = build_reference_oracle_bin(problem_dir, force=force_oracle)
    if not oracle_bin:
        msg = f"reference oracle: {oerr}"
        update_status(statuses, pid, "error", msg)
        print(f"[{pid}] ERROR: reference oracle: {oerr[:500]}", file=sys.stderr)
        append_pipeline_error(error_source, pid, "reference_oracle_build", msg)
        return "error"
    ot = oracle_timeout if oracle_timeout is not None else timeout
    input_jsonl = "\n".join(json.dumps(c) for c in cases) + "\n"
    try:
        hresult = subprocess.run(
            [str(oracle_bin)], input=input_jsonl,
            capture_output=True, text=True, timeout=ot,
        )
    except subprocess.TimeoutExpired:
        msg = f"reference oracle timed out ({ot}s)"
        update_status(statuses, pid, "error", msg)
        print(f"[{pid}] ERROR: reference oracle timed out", file=sys.stderr)
        append_pipeline_error(error_source, pid, "reference_oracle_timeout", msg)
        return "error"
    if hresult.returncode != 0:
        err = (hresult.stderr or "")[:8000]
        msg = f"reference oracle failed:\n{err}"
        update_status(statuses, pid, "error", msg)
        print(f"[{pid}] ERROR: reference oracle rc={hresult.returncode}", file=sys.stderr)
        first_line = input_jsonl.split("\n", 1)[0] if input_jsonl.strip() else ""
        append_pipeline_error(
            error_source,
            pid,
            "reference_oracle_run",
            msg,
            extra={"returncode": hresult.returncode, "first_input_jsonl_line": first_line[:4000]},
        )
        return "error"
    output_cases: list[dict] = []
    for line in hresult.stdout.splitlines():
        line = line.strip()
        if line:
            try:
                output_cases.append(json.loads(line))
            except json.JSONDecodeError:
                pass
    if output_cases:
        cases = output_cases
        print(f"[{pid}] reference oracle computed outputs for {len(cases)} cases")
    else:
        msg = "reference oracle produced no parseable JSON lines"
        update_status(statuses, pid, "error", msg)
        print(f"[{pid}] ERROR: reference oracle produced no parseable output", file=sys.stderr)
        append_pipeline_error(error_source, pid, "reference_oracle_no_output", msg)
        return "error"

    # Deduplicate
    seen: set[str] = set()
    unique: list[dict] = []
    for c in cases:
        key = json.dumps(c, sort_keys=True)
        if key not in seen:
            seen.add(key)
            unique.append(c)
    cases = unique

    tc_path = tests_dir / "adv_testcase.json"
    with open(tc_path, "w") as f:
        f.write("[\n")
        for i, c in enumerate(cases):
            comma = "," if i < len(cases) - 1 else ""
            f.write("  " + json.dumps(c, separators=(",", ": ")) + comma + "\n")
        f.write("]\n")

    update_status(statuses, pid, "done", test_count=len(cases))
    print(f"[{pid}] done: {len(cases)} test cases written")
    return "done"


async def generate_and_verify_async(
    info: ProblemInfo,
    example_code: str,
    client: Any,
    statuses: dict[str, ProblemStatus],
    status_lock: asyncio.Lock,
    worker_sem: asyncio.Semaphore,
    verus_bin: str,
    max_retries: int,
    run_timeout: int,
    verus_timeout: int,
    oracle_timeout: int,
) -> str:
    pid = info.problem_id
    tests_dir = info.problem_dir / "tests"
    tests_dir.mkdir(parents=True, exist_ok=True)

    base_user_prompt = build_verus_user_prompt(info, example_code)

    async with worker_sem:
        last_error = ""
        for attempt in range(1, max_retries + 1):
            print(f"[{pid}] attempt {attempt}/{max_retries}: calling LLM ...")
            async with status_lock:
                update_status(statuses, pid, "generating", attempt=attempt)
                save_status(statuses)

            messages: list[dict[str, str]] = [
                {"role": "system", "content": VERUS_SYSTEM_PROMPT},
                {"role": "user", "content": base_user_prompt},
            ]
            if last_error:
                messages.append({"role": "user", "content": build_verus_followup_prompt(last_error)})

            try:
                response_text = await async_chat_completion(client, messages)
            except Exception as e:
                last_error = f"API error: {e}"
                print(f"[{pid}] attempt {attempt}: {last_error}")
                async with status_lock:
                    update_status(statuses, pid, "retrying", last_error, attempt=attempt)
                    save_status(statuses)
                continue

            code = extract_rust_code(response_text)
            if not code:
                last_error = "No ```rust block in response"
                print(f"[{pid}] attempt {attempt}: {last_error}")
                async with status_lock:
                    update_status(statuses, pid, "retrying", last_error, attempt=attempt)
                    save_status(statuses)
                continue

            gen_rs = tests_dir / GEN_ADV_RS_NAME
            gen_rs.write_text(code)

            print(f"[{pid}] attempt {attempt}: verifying with verus ...")
            status, detail = verify_with_verus(gen_rs, verus_bin, verus_timeout)

            if status == "verified":
                print(f"[{pid}] attempt {attempt}: VERIFIED")
                async with status_lock:
                    update_status(statuses, pid, "verified", attempt=attempt)
                    save_status(statuses)

                gen_bin = tests_dir / GEN_ADV_BIN_NAME
                default_bin = tests_dir / gen_rs.stem
                if not gen_bin.exists() and default_bin.exists():
                    default_bin.rename(gen_bin)

                result_stage = collect_test_cases(
                    pid,
                    gen_bin,
                    tests_dir,
                    run_timeout,
                    statuses,
                    error_source="run-async",
                    oracle_timeout=oracle_timeout,
                )
                async with status_lock:
                    save_status(statuses)
                return result_stage

            first_line = detail.split('\n')[0][:120] if detail else "unknown error"
            print(f"[{pid}] attempt {attempt}: verify_error: {first_line}")
            last_error = detail
            async with status_lock:
                update_status(statuses, pid, "retrying", detail, attempt=attempt)
                save_status(statuses)

        print(f"[{pid}] failed after {max_retries} attempts")
        async with status_lock:
            update_status(statuses, pid, "failed_after_retries", last_error, attempt=max_retries)
            save_status(statuses)
        append_pipeline_error(
            "run-async",
            pid,
            "failed_after_retries",
            (last_error or "")[:32000],
            extra={"max_retries": max_retries},
        )
        return "failed_after_retries"


def cmd_run_async(args: argparse.Namespace) -> int:
    if args.max_retries < 1 or args.max_retries > 10:
        print("--max-retries must be between 1 and 10.", file=sys.stderr)
        return 1

    verus_bin = find_verus_binary(args.verus)
    if not verus_bin:
        print(
            f"Could not find `verus` binary. Set ``VERUS``, pass ``--verus``, or install at ``{DEFAULT_VERUS_BINARY}``.",
            file=sys.stderr,
        )
        return 1

    try:
        from anthropic import AsyncAnthropic
    except ImportError:
        print("anthropic package not installed. Run: pip install anthropic", file=sys.stderr)
        return 1

    limit = args.debug if args.debug is not None else args.limit
    problems = iter_problems(args.kind)
    if args.problem:
        wanted = set(args.problem)
        problems = [p for p in problems if p.name in wanted]
    if limit:
        problems = problems[:limit]
    if not problems:
        print("No problems found.", file=sys.stderr)
        return 1

    infos: list[ProblemInfo] = []
    load_errors = 0
    skipped_existing = 0
    for pdir in problems:
        try:
            existing = pdir / "tests" / GEN_ADV_RS_NAME
            if existing.exists() and not args.force:
                skipped_existing += 1
                continue
            infos.append(load_problem(pdir))
        except Exception as e:
            print(f"[error] {pdir.name}: {e}", file=sys.stderr)
            load_errors += 1
    if skipped_existing:
        print(f"Skipped {skipped_existing} problems with existing {GEN_ADV_RS_NAME} (use --force to overwrite)")

    if not infos:
        print("No valid problems found.", file=sys.stderr)
        if skipped_existing:
            print(
                "\nHint: every selected problem already has tests/gen_adv.rs. "
                "run-async only *generates* that file via the LLM.\n"
                "To build tests/adv_testcase.json from existing gen_adv.rs + code.rs, run:\n"
                "  python3 test_gen/gen_testcases.py materialize --kind both --limit 0\n"
                "(add --seed N, --force-compile, --verus, --oracle-timeout … as needed)\n",
                file=sys.stderr,
            )
        return 1

    example_code = ""
    if EXAMPLE_GEN_ADV_PATH.exists():
        example_code = EXAMPLE_GEN_ADV_PATH.read_text()

    statuses = load_status()
    total_r = len(infos)
    run_t0 = time.monotonic()

    async def runner() -> list[str]:
        client = AsyncAnthropic()
        status_lock = asyncio.Lock()
        worker_sem = asyncio.Semaphore(args.concurrency)
        done_r = 0
        prog_lock = asyncio.Lock()

        async def run_one(info: ProblemInfo) -> str:
            nonlocal done_r
            r = await generate_and_verify_async(
                info=info,
                example_code=example_code,
                client=client,
                statuses=statuses,
                status_lock=status_lock,
                worker_sem=worker_sem,
                verus_bin=verus_bin,
                max_retries=args.max_retries,
                run_timeout=args.timeout,
                verus_timeout=args.verus_timeout,
                oracle_timeout=args.oracle_timeout,
            )
            async with prog_lock:
                done_r += 1
                elapsed = time.monotonic() - run_t0
                print(
                    f"[progress {done_r}/{total_r}] {info.problem_id} -> {r} "
                    f"({elapsed:.1f}s elapsed)",
                    flush=True,
                )
            return r

        return await asyncio.gather(*[run_one(info) for info in infos])

    log_path = Path(os.environ.get("GEN_PIPELINE_ERROR_LOG", str(_DEFAULT_PIPELINE_ERROR_LOG)))
    print(
        f"Running async Verus-verified generation for {total_r} problems "
        f"(concurrency={args.concurrency}, max_retries={args.max_retries}) — "
        f"watch [progress completed/total] lines below",
        flush=True,
    )
    print(f"Failures append to: {log_path} (GEN_PIPELINE_ERROR_LOG)", flush=True)
    if load_errors:
        print(f"  {load_errors} problems failed to load")

    results = asyncio.run(runner())
    save_status(statuses)
    print(
        f"run-async wall time: {time.monotonic() - run_t0:.1f}s for {total_r} problem(s)",
        flush=True,
    )

    counts: dict[str, int] = {}
    failed_ids: list[str] = []
    for info, r in zip(infos, results):
        counts[r] = counts.get(r, 0) + 1
        if r in ("failed_after_retries", "error"):
            failed_ids.append(info.problem_id)

    print("\nResults:")
    for key in sorted(counts):
        print(f"  {key:24s} {counts[key]}")

    failed_md = REPO_ROOT / "test_gen" / "failed.md"
    if failed_ids:
        failed_ids.sort()
        with open(failed_md, "w") as f:
            f.write("# Failed problems\n\n")
            for pid in failed_ids:
                err = statuses[pid].error.split('\n')[0][:120] if pid in statuses else ""
                f.write(f"- `{pid}` {err}\n")
        print(f"\n{len(failed_ids)} failures written to {failed_md}")
    elif failed_md.exists():
        failed_md.unlink()

    return 0


# ---------------------------------------------------------------------------
# Subcommand: retry
# ---------------------------------------------------------------------------

def cmd_retry(args: argparse.Namespace) -> int:
    statuses = load_status()
    failed = {pid: s for pid, s in statuses.items()
              if s.stage == "error" and s.attempt < args.max_retries}

    if not failed:
        print("No retryable failures found.")
        return 0

    print(f"Found {len(failed)} failures to retry (attempt limit: {args.max_retries})")

    # Build retry JSONL with error feedback
    retry_path = GEN_DIR / "batch_retry_input.jsonl"
    count = 0
    with open(retry_path, "w") as f:
        for pid, st in failed.items():
            # Find problem dir
            problem_dir = None
            for kind_dir in (BENCH_ROOT / "leetcode", BENCH_ROOT / "codeforces"):
                pdir = kind_dir / pid
                if pdir.exists():
                    problem_dir = pdir
                    break
            if not problem_dir:
                continue

            try:
                info = load_problem(problem_dir)
            except Exception:
                continue

            # Build retry prompt with error feedback
            original_prompt = build_user_prompt(info)
            error_feedback = f"""

== PREVIOUS ATTEMPT FAILED ==
The previous generator had this error:
{st.error}

Please fix the issue and generate a corrected program.
Common fixes:
- If compilation failed, check for syntax errors or missing imports.
- If the generator crashed, check for panics (index out of bounds, overflow).
- If no valid JSON was produced, ensure println! outputs valid JSON objects.
- Ensure all inputs satisfy the `requires` clause constraints.
"""
            req = {
                "custom_id": pid,
                "method": "POST",
                "url": "/v1/chat/completions",
                "body": {
                    "model": MODEL,
                    "messages": [
                        {"role": "system", "content": SYSTEM_PROMPT},
                        {"role": "user", "content": original_prompt + error_feedback},
                    ],
                    "temperature": TEMPERATURE,
                    "max_completion_tokens": MAX_TOKENS,
                },
            }
            f.write(json.dumps(req) + "\n")
            update_status(statuses, pid, "prompted", attempt=st.attempt + 1)
            count += 1

    save_status(statuses)
    print(f"Wrote {count} retry requests -> {retry_path}")
    print(f"Now run: submit --input {retry_path}")
    return 0


# ---------------------------------------------------------------------------
# Subcommand: status
# ---------------------------------------------------------------------------

def cmd_status(args: argparse.Namespace) -> int:
    statuses = load_status()
    if not statuses:
        print("No status data. Run `prepare` first.")
        return 0

    counts: dict[str, int] = {}
    for s in statuses.values():
        counts[s.stage] = counts.get(s.stage, 0) + 1

    total = len(statuses)
    print(f"Total problems tracked: {total}")
    print()
    ordered_stages = [
        "discovered", "prompted", "generating", "generated", "compiled",
        "verified", "retrying", "ran", "validated", "output_computed",
        "done", "failed_after_retries", "error",
    ]
    for stage in ordered_stages:
        c = counts.get(stage, 0)
        if c:
            pct = 100 * c / total
            bar = "#" * int(pct / 2)
            print(f"  {stage:20s} {c:5d} ({pct:5.1f}%) {bar}")

    # Show error breakdown
    error_problems = [s for s in statuses.values() if s.stage == "error"]
    if error_problems and args.verbose:
        print(f"\nError details ({len(error_problems)} problems):")
        # Categorize errors
        categories: dict[str, list[str]] = {}
        for s in error_problems:
            cat = s.error.split("\n")[0][:60] if s.error else "unknown"
            categories.setdefault(cat, []).append(s.problem_id)
        for cat, pids in sorted(categories.items(), key=lambda x: -len(x[1])):
            print(f"  [{len(pids):3d}] {cat}")
            if len(pids) <= 5:
                print(f"        {', '.join(pids)}")

    return 0


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = ap.add_subparsers(dest="command", required=True)

    # prepare
    p_prepare = sub.add_parser("prepare", help="Discover problems, build prompts, write batch JSONL")
    p_prepare.add_argument("--kind", choices=("leetcode", "codeforces", "both"),
                           default="both")
    p_prepare.add_argument("--problem", nargs="+", metavar="ID",
                           help="Only include these problem IDs (e.g. lc1 cf116A)")
    p_prepare.add_argument("--limit", type=int, default=None,
                           help="Only include the first N problems (for debugging)")

    # submit
    p_submit = sub.add_parser("submit", help="Upload JSONL and create batch")
    p_submit.add_argument("--input", type=Path, default=None,
                          help="Override input JSONL path (for retries)")

    # poll
    p_poll = sub.add_parser("poll", help="Poll batch status and download results")
    p_poll.add_argument("--interval", type=int, default=60,
                        help="Polling interval in seconds")

    # validate
    p_validate = sub.add_parser("validate", help="Parse responses, compile, run, compute outputs")
    p_validate.add_argument("--workers", type=int, default=1,
                            help="Number of parallel workers")
    p_validate.add_argument(
        "--timeout",
        type=int,
        default=600,
        help="Timeout for gen_adv_bin (generator) run in seconds (default: 600).",
    )
    p_validate.add_argument(
        "--oracle-timeout",
        type=int,
        default=DEFAULT_REFERENCE_ORACLE_TIMEOUT_S,
        help=(
            "Timeout for reference oracle (code.rs stdin/stdout) in seconds "
            f"(default: {DEFAULT_REFERENCE_ORACLE_TIMEOUT_S}). "
            "Independent of --timeout so a short generator cap does not cap ground truth."
        ),
    )

    # materialize
    p_mat = sub.add_parser(
        "materialize",
        help="Build tests/adv_testcase.json from gen_adv.rs; outputs via include!(../code.rs) oracle",
    )
    p_mat.add_argument("--kind", choices=("leetcode", "codeforces", "both"),
                       default="both")
    p_mat.add_argument("--problem", nargs="+", metavar="ID",
                       help="Only these problem IDs (e.g. cf1A lc42)")
    p_mat.add_argument("--limit", type=int, default=None,
                       help="Process at most N problems (omit or use 0 for no cap / full set)")
    p_mat.add_argument("--seed", default="42",
                       help="Seed argument passed to gen_adv_bin (default: 42)")
    p_mat.add_argument(
        "--verus",
        default=None,
        help=f"Path to verus binary (else VERUS env, then {DEFAULT_VERUS_BINARY} if present, then PATH)",
    )
    p_mat.add_argument(
        "--timeout",
        type=int,
        default=30,
        help=(
            "Timeout for gen_adv_bin (generator) run in seconds. "
            "Older versions also applied this to the reference oracle; use --oracle-timeout for that now."
        ),
    )
    p_mat.add_argument(
        "--oracle-timeout",
        type=int,
        default=DEFAULT_REFERENCE_ORACLE_TIMEOUT_S,
        help=(
            "Timeout for reference oracle (ground truth on all generated inputs) in seconds "
            f"(default: {DEFAULT_REFERENCE_ORACLE_TIMEOUT_S}). "
            "To keep a previous 90s oracle cap, pass --oracle-timeout 90 (generator stays --timeout)."
        ),
    )
    p_mat.add_argument("--verus-timeout", type=int, default=600,
                       help="Timeout for verus --compile when rustc fails")
    p_mat.add_argument("--rustc-timeout", type=int, default=60,
                       help="Timeout for rustc when compiling gen_adv.rs")
    p_mat.add_argument("--force-compile", action="store_true",
                       help="Recompile gen_adv even if gen_adv_bin already exists")
    p_mat.add_argument("--force-oracle", action="store_true",
                       help="Recompile reference_oracle (include! code.rs) even if binary is fresh")

    # run-async (Verus-verified generation with repair loop)
    p_async = sub.add_parser(
        "run-async",
        help="Generate Verus-verified generators with async API and repair loop",
    )
    p_async.add_argument("--kind", choices=("leetcode", "codeforces", "both"),
                         default="both")
    p_async.add_argument("--problem", nargs="+", metavar="ID",
                         help="Only include these problem IDs (e.g. lc1 cf116A)")
    p_async.add_argument("--limit", type=int, default=20,
                         help="Only include the first N problems (default: 20, 0 for all)")
    p_async.add_argument(
        "--verus",
        default=None,
        help=f"Path to verus binary (else VERUS env, then {DEFAULT_VERUS_BINARY}, then PATH)",
    )
    p_async.add_argument("--concurrency", type=int,
                         default=int(os.environ.get("GEN_CONCURRENCY", "100")),
                         help="Number of problems to process concurrently")
    p_async.add_argument("--max-retries", type=int, default=5,
                         help="Maximum repair attempts per problem (1-10)")
    p_async.add_argument("--force", action="store_true",
                         help="Overwrite existing gen_adv.rs files")
    p_async.add_argument("--debug", type=int, default=None, metavar="N",
                         help="Shorthand for --limit N (e.g. --debug 20)")
    p_async.add_argument(
        "--timeout",
        type=int,
        default=30,
        help="Timeout for gen_adv_bin (generator) run in seconds (default: 30).",
    )
    p_async.add_argument(
        "--oracle-timeout",
        type=int,
        default=DEFAULT_REFERENCE_ORACLE_TIMEOUT_S,
        help=(
            "Timeout for reference oracle (code.rs on all generated inputs) in seconds "
            f"(default: {DEFAULT_REFERENCE_ORACLE_TIMEOUT_S})."
        ),
    )
    p_async.add_argument("--verus-timeout", type=int, default=600,
                         help="Timeout per verus verification in seconds")

    # retry
    p_retry = sub.add_parser("retry", help="Collect failures and build retry batch")
    p_retry.add_argument("--max-retries", type=int, default=3,
                         help="Maximum retry attempts per problem")

    # status
    p_status = sub.add_parser("status", help="Show per-problem status summary")
    p_status.add_argument("-v", "--verbose", action="store_true",
                          help="Show error details")

    args = ap.parse_args()

    if args.command == "prepare":
        return cmd_prepare(args)
    elif args.command == "submit":
        return cmd_submit(args)
    elif args.command == "poll":
        return cmd_poll(args)
    elif args.command == "validate":
        return cmd_validate(args)
    elif args.command == "materialize":
        return cmd_materialize(args)
    elif args.command == "run-async":
        return cmd_run_async(args)
    elif args.command == "retry":
        return cmd_retry(args)
    elif args.command == "status":
        return cmd_status(args)
    else:
        ap.print_help()
        return 1


if __name__ == "__main__":
    sys.exit(main())
