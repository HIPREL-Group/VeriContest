"""The component checks: code_tests, verus, and spec_tests.

Each check returns a dict with ``status`` (pass, fail, timeout, error) plus
diagnostic fields.
"""
from __future__ import annotations

import json
import math
import os
import re
import shutil
import subprocess
from pathlib import Path

from . import harness
from .config import LIMITS, REPO_ROOT, VERUS_BIN, VERUS_FLAGS
from .problems import load_checker, load_jsonl, problem_dir, testcase_file


def _tail(text: str | None, n: int = 4000) -> str:
    return (text or "")[-n:]


def _run(cmd: list[str], timeout: float, **kw) -> subprocess.CompletedProcess | None:
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, **kw)
    except subprocess.TimeoutExpired:
        return None


# -----------------------------------------------------------------------------
# verus (End2End and ProofGen)
# -----------------------------------------------------------------------------
def verify(program: str, workdir: Path) -> dict:
    src = workdir / "verify.rs"
    src.write_text(program)
    cp = _run([str(VERUS_BIN), *VERUS_FLAGS, str(src)], LIMITS["verify_timeout_sec"])
    if cp is None:
        return {"status": "timeout"}
    if cp.returncode != 0:
        return {"status": "fail", "log": _tail(cp.stderr + cp.stdout)}
    return {"status": "pass"}


# Verus syntax newer than lynette's parser (syn_verus at verus f0662d3): the
# ``returns`` clause (six problems' code_spec.rs) and an ``ensures`` block
# expression (three golds' lemmas). Both sides of a comparison are rewritten
# the same way, into forms it parses and still compares.
_RETURNS = re.compile(r"^[ \t]*returns\b", re.M)
_AFTER_RETURNS = re.compile(r"\b(?:decreases|opens_invariants|no_unwind)\b")
_BEFORE_RETURNS = re.compile(r"\b(requires|recommends|ensures)\b|\bfn\b")
_ENSURES_BLOCK = re.compile(r"\bensures\s*\{")


def lynette_compatible(code: str) -> str:
    if _ENSURES_BLOCK.search(code):
        code = _paren_ensures_blocks(code)
    if _RETURNS.search(code):
        code = _returns_into_ensures(code)
    return code


def _paren_ensures_blocks(code: str) -> str:
    """``ensures { let ..; e },`` (a block expression) -> ``ensures ({ .. }),``."""
    out, pos = [], 0
    for m in _ENSURES_BLOCK.finditer(code):
        open_i = m.end() - 1
        if open_i < pos:
            continue
        end = _parse_balanced_from(code, open_i, "{", "}")
        if end is None or not code[end:].lstrip().startswith(","):
            continue
        out.append(code[pos:open_i] + "(" + code[open_i:end] + ")")
        pos = end
    out.append(code[pos:])
    return "".join(out)


def _returns_into_ensures(code: str) -> str:
    """``returns e,`` -> ``ensures __lynette_returns(e),``, merged into the
    function's ``ensures`` when it has one (Verus puts ``ensures`` directly
    before ``returns``)."""
    out, pos = [], 0
    for m in _RETURNS.finditer(code):
        # The expression runs to the body's ``{`` (or ``;``, or a later
        # clause) outside any brackets.
        depth = 0
        for end in range(m.end(), len(code)):
            c = code[end]
            if depth == 0 and (c in "{;" or _AFTER_RETURNS.match(code, end)):
                break
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
        else:
            continue
        expr = code[m.end():end].strip().rstrip(",").strip()
        marker = f"__lynette_returns({expr}),\n"
        clause = None
        for k in _BEFORE_RETURNS.finditer(code, pos, m.start()):
            clause = k.group(1)
        if clause == "ensures":
            head = code[pos:m.start()].rstrip()
            out.append(head + ("\n" if head.endswith(",") else ",\n") + marker)
        else:
            out.append(code[pos:m.start()] + "ensures " + marker)
        pos = end
    out.append(code[pos:])
    return "".join(out)


def preserved(original: str, candidate: str, workdir: Path, lynette: str) -> dict:
    """ProofGen: code and specification unchanged (``lynette compare -t``)."""
    a, b = workdir / "original.rs", workdir / "candidate.rs"
    a.write_text(lynette_compatible(original))
    b.write_text(lynette_compatible(candidate))
    cp = _run([lynette, "compare", "-t", str(a), str(b)], LIMITS["compare_timeout_sec"])
    if cp is None:
        return {"status": "fail", "log": "lynette compare timed out"}
    if cp.returncode == 0:
        return {"status": "pass"}
    if cp.returncode == 1 and cp.stdout.strip() == "Files are different":
        return {"status": "fail", "log": "unsafe code or spec change"}
    return {"status": "fail", "log": "lynette could not compare: " + _tail(cp.stderr + cp.stdout)}


def lynette_path() -> str | None:
    env = os.environ.get("VCEVAL_LYNETTE")
    if env:
        return env
    bundled = REPO_ROOT / "evaluation" / "tools" / "lynette"
    if bundled.is_file():
        return str(bundled)
    return shutil.which("lynette")


# -----------------------------------------------------------------------------
# code_tests (CodeGen and End2End)
# -----------------------------------------------------------------------------
def _stdin_for(case: dict, mode: str) -> str:
    # Only the input reaches the program; the expected output never does.
    if mode == "oracle":
        return json.dumps({"input": case["input"]}, ensure_ascii=False) + "\n"
    inp = case.get("input")
    return inp if isinstance(inp, str) else json.dumps(inp, ensure_ascii=False)


def _outputs_match(expected, actual) -> bool:
    """Compare JSON values without coercing integers, booleans, or strings.

    Only a floating-point reference answer permits numerical tolerance.
    Apply the same rules recursively to structured outputs.
    """
    if type(expected) is bool:
        return type(actual) is bool and expected == actual
    if type(expected) is int:
        return type(actual) is int and expected == actual
    if type(expected) is float:
        if type(actual) not in (int, float) or not math.isfinite(expected):
            return False
        try:
            return math.isfinite(actual) and abs(expected - actual) <= 1e-6 * max(1.0, abs(expected))
        except OverflowError:
            return False
    if type(expected) is str:
        return type(actual) is str and expected.strip() == actual.strip()
    if type(expected) is list:
        return (type(actual) is list and len(expected) == len(actual)
                and all(_outputs_match(a, b) for a, b in zip(expected, actual)))
    if type(expected) is dict:
        return (type(actual) is dict and expected.keys() == actual.keys()
                and all(_outputs_match(value, actual[key]) for key, value in expected.items()))
    if expected is None:
        return actual is None
    return False


def _json_output_line(stdout: str) -> dict | None:
    for ln in stdout.split("\n"):
        ln = ln.strip()
        if ln.startswith("{"):
            try:
                return json.loads(ln)
            except ValueError:
                continue
    return None


def code_tests(problem_id: str, program: str, policy: str, testcases_root: Path, workdir: Path) -> dict:
    path = testcase_file(testcases_root, problem_id, "testcases.jsonl")
    if not path.is_file():
        return {"status": "error", "log": f"missing testcases: {path}"}
    try:
        backend, source = harness.build_source(problem_dir(problem_id), program, policy)
    except harness.HarnessError as exc:
        return {"status": "fail", "log": f"harness build error: {exc}"}
    src, binary = workdir / "main.rs", workdir / "main"
    src.write_text(source)
    if backend == "verus":
        # -O as for rustc below: unoptimized builds can miss the time limit.
        cmd = [str(VERUS_BIN), "--no-verify", "--compile", str(src), "-o", str(binary), "-O"]
    else:
        cmd = [os.environ.get("VCEVAL_RUSTC", "rustc"), "--edition", "2021", "-O", str(src), "-o", str(binary)]
    cp = _run(cmd, LIMITS["compile_timeout_sec"])
    if cp is None:
        return {"status": "fail", "backend": backend, "log": "compile timeout"}
    if cp.returncode != 0:
        return {"status": "fail", "backend": backend, "log": "compile error\n" + _tail(cp.stderr + cp.stdout, 3000)}

    mode, _ = harness.template(problem_dir(problem_id))
    # Problems with several valid answers ship tests/checker.py (benchmark/CHECKERS.md).
    checker = load_checker(problem_id)
    cases = [c for c in load_jsonl(path) if "output" in c]
    passed, timeouts, runtime_errors, failures = 0, 0, 0, []
    for i, case in enumerate(cases):
        try:
            rp = subprocess.run([str(binary)], input=_stdin_for(case, mode), capture_output=True,
                                text=True, timeout=LIMITS["case_timeout_sec"])
        except subprocess.TimeoutExpired:
            timeouts += 1
            failures.append({"case": i, "reason": "timeout"})
            continue
        if rp.returncode != 0:
            runtime_errors += 1
            failures.append({"case": i, "reason": "runtime_error", "stderr": rp.stderr[-300:]})
            continue
        row = _json_output_line(rp.stdout) if mode == "oracle" else None
        if row is not None and "output" in row:
            actual = row["output"]
        elif mode == "main" or isinstance(case.get("output"), str):
            actual = rp.stdout
        else:
            failures.append({"case": i, "reason": "no_parseable_output"})
            continue
        if checker is not None:
            try:
                ok = bool(checker(case["input"], actual))
            except Exception:
                ok = False
        else:
            ok = _outputs_match(case["output"], actual)
        if ok:
            passed += 1
        else:
            failures.append({"case": i, "expected": case.get("output"), "actual": actual})
    status = "pass" if cases and passed == len(cases) else "fail"
    return {"status": status, "backend": backend, "passed": passed, "total": len(cases),
            "timeouts": timeouts, "runtime_errors": runtime_errors,
            "judge": "checker" if checker else "exact", "failed_cases": _short(failures)}


def _short(failures: list[dict]) -> list[dict]:
    out = []
    for f in failures[:5]:
        out.append({k: (v if len(json.dumps(v, default=str)) <= 500 else json.dumps(v, default=str)[:500] + "...")
                    for k, v in f.items()})
    return out


# -----------------------------------------------------------------------------
# spec_tests for SpecGen: parse + typecheck with stubbed bodies
# -----------------------------------------------------------------------------
def _parse_balanced_from(s: str, start: int, open_c: str, close_c: str) -> int | None:
    if start >= len(s) or s[start] != open_c:
        return None
    depth = 0
    for i in range(start, len(s)):
        if s[i] == open_c:
            depth += 1
        elif s[i] == close_c:
            depth -= 1
            if depth == 0:
                return i + 1
    return None


_FN_ITEM = re.compile(r"\bfn\s+[A-Za-z_]\w*")
_GHOST_FN = re.compile(r"\b(?:spec|proof)\b[^\n;{}]*$")
# After a brace group in a signature (e.g. `decreases if c { a } else { b },`)
# more signature follows; after the body, the next item or the enclosing `}`.
_SIG_GOES_ON = re.compile(r"(?:else\b|[,{(\[.?&|^*/%+=<>!-]|"
                          r"(?:requires|ensures|recommends|decreases|when|via|returns|opens_invariants|no_unwind)\b)")


def _skip_comment_or_literal(code: str, i: int) -> int:
    """Index just past a comment, string or char literal starting at ``i``, else ``i``."""
    if code.startswith("//", i):
        j = code.find("\n", i)
        return len(code) if j == -1 else j
    if code.startswith("/*", i):
        j = code.find("*/", i + 2)
        return len(code) if j == -1 else j + 2
    if code[i] == '"':
        j = i + 1
        while j < len(code) and code[j] != '"':
            j += 2 if code[j] == "\\" else 1
        return j + 1
    m = re.match(r"'(?:\\.|\\u\{[0-9a-fA-F]+\}|[^\\'])'", code[i:i + 12]) if code[i] == "'" else None
    return i + m.end() if m else i


def _matching_brace(code: str, open_i: int) -> int | None:
    depth, i = 0, open_i
    while i < len(code):
        j = _skip_comment_or_literal(code, i)
        if j != i:
            i = j
            continue
        if code[i] == "{":
            depth += 1
        elif code[i] == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


def _past_space_and_comments(code: str, k: int) -> int:
    while True:
        while k < len(code) and code[k].isspace():
            k += 1
        if not code.startswith(("//", "/*"), k):
            return k
        k = _skip_comment_or_literal(code, k)


def _fn_body(code: str, i: int) -> tuple[int, int] | None:
    """``(open, close)`` of the body of the fn whose header starts at ``i``;
    ``None`` for a bodiless declaration."""
    depth = 0
    while i < len(code):
        j = _skip_comment_or_literal(code, i)
        if j != i:
            i = j
            continue
        c = code[i]
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        elif c == ";" and depth == 0:
            return None
        elif c == "{" and depth == 0:
            close = _matching_brace(code, i)
            if close is None:
                return None
            if not _SIG_GOES_ON.match(code, _past_space_and_comments(code, close + 1)):
                return i, close
            i = close
        i += 1
    return None


def stub_exec_bodies(code: str) -> str:
    """Replace every executable fn body (any impl, any return type) with
    ``loop {}``, which has every type, so ``verus --no-verify`` checks only the
    specification. Spec and proof fns are kept."""
    out, pos = [], 0
    for m in _FN_ITEM.finditer(code):
        if m.start() < pos:
            continue
        line_start = code.rfind("\n", 0, m.start()) + 1
        prefix = code[line_start:m.start()]
        if prefix.lstrip().startswith("//") or _GHOST_FN.search(prefix):
            continue
        body = _fn_body(code, m.end())
        if body is None:
            continue
        out.append(code[pos:body[0]] + "{ loop {} }")
        pos = body[1] + 1
    return "".join(out) + code[pos:]


def typecheck_spec(program: str, workdir: Path) -> dict:
    src = workdir / "spec_typecheck.rs"
    src.write_text(stub_exec_bodies(program))
    cp = _run([str(VERUS_BIN), "--no-verify", str(src)], LIMITS["typecheck_timeout_sec"])
    if cp is None:
        return {"status": "timeout"}
    if cp.returncode != 0:
        return {"status": "fail", "log": _tail(cp.stderr + cp.stdout)}
    return {"status": "pass"}
