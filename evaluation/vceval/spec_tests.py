"""spec_tests for SpecGen and End2End: test a specification on the problem's
test cases with post2exe.

post2exe lowers the postcondition (and precondition) of the specified function
into an executable checker. A good specification accepts every positive test
case (input, reference output) and rejects every negative one (same input,
wrong output). The reference ``spec.rs`` is run the same way first: where
post2exe cannot test it cleanly, or cannot test the answer's specification, the
result is ``unsupported`` and left to human review.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

from .config import LIMITS, REPO_ROOT, VERUS_BIN
from .problems import problem_dir, testcase_file

POST2EXE_DIR = REPO_ROOT / "post2exe"

# post2exe calls the positive phase "soundness" and the negative one "completeness".
_PHASES = {"positive": "--soundness", "negative": "--completeness"}
_RESULT = re.compile(r"^\[(soundness|completeness)\] (PASS|FAIL|EMPTY):(.*)$", re.M)


def _run(cmd: list[str], timeout: float) -> subprocess.CompletedProcess | None:
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None


def _phase(stdout: str) -> dict | None:
    m = _RESULT.search(stdout)
    if not m:
        return None
    rest = m.group(3)
    counts = re.search(r"(\d+) / (\d+)", rest)
    unparsed = re.search(r"skipped (\d+) parse-failed lines", rest)
    unexpected, scored = (int(counts.group(1)), int(counts.group(2))) if counts else (0, 0)
    return {"result": m.group(2), "scored": scored,
            "unexpected": unexpected if m.group(2) == "FAIL" else 0,
            "unparsed": int(unparsed.group(1)) if unparsed else 0}


def run_post2exe(problem_id: str, program: str, testcases_root: Path, workdir: Path) -> dict:
    """Lower ``program``'s specification with post2exe and run the checker on the
    positive and negative test cases. ``stage`` is where it stopped."""
    pdir = workdir / "post2exe" / problem_id  # <family>/<problem>: post2exe reads the family from the path
    tests = pdir / "tests"
    tests.mkdir(parents=True, exist_ok=True)
    (pdir / "spec.rs").write_text(program)
    main_rs = problem_dir(problem_id) / "main.rs"  # Codeforces stdin layout
    if main_rs.is_file():
        shutil.copy(main_rs, pdir / "main.rs")
    for name in ("testcases.jsonl", "mutated_testcases.jsonl"):
        f = testcase_file(testcases_root, problem_id, name)
        if not f.is_file():
            return {"stage": "missing_testcases", "detail": str(f)}
        (tests / name).symlink_to(f.resolve())
    checker, binary = tests / "test_post.rs", pdir / "checker"
    gen = _run([os.environ.get("VCEVAL_POST2EXE_PYTHON", sys.executable), str(POST2EXE_DIR / "gen_post2exe.py"),
                "--problem", str(pdir), "--force"], LIMITS["spec_generate_timeout_sec"])
    if gen is None:
        return {"stage": "timeout", "phase": "generate"}
    if "No module named" in gen.stderr:  # environment, not the specification
        return {"stage": "environment", "detail": gen.stderr[-500:]}
    if not checker.is_file():
        blockers = [l.split("]: ", 1)[-1] for l in gen.stderr.splitlines() if "WARN [" in l]
        return {"stage": "generate", "detail": "; ".join(blockers or [gen.stderr.strip()[-300:]])[-1000:]}
    code = checker.read_text()
    backend = "direct" if code.startswith("// post2exe-backend: direct") else "macro"
    cmd = ([os.environ.get("VCEVAL_RUSTC", "rustc"), "--edition=2021", "-O", str(checker), "-o", str(binary)]
           if backend == "direct" else [str(VERUS_BIN), "--compile", str(checker), "-o", str(binary)])
    cp = _run(cmd, LIMITS["spec_compile_timeout_sec"])
    if cp is None:
        return {"stage": "timeout", "backend": backend, "phase": "compile"}
    if cp.returncode != 0:
        return {"stage": "compile", "backend": backend, "detail": (cp.stderr + cp.stdout)[-1000:]}
    phases = {}
    for name, flag in _PHASES.items():
        rp = _run([str(binary), flag], LIMITS["spec_test_timeout_sec"])
        if rp is None:
            return {"stage": "timeout", "backend": backend, "phase": name}
        parsed = _phase(rp.stdout)
        if parsed is None:
            return {"stage": "run", "backend": backend, "phase": name, "detail": (rp.stdout + rp.stderr)[-1000:]}
        phases[name] = parsed
    return {"stage": "ran", "backend": backend, "phases": phases}


# Why a specification goes to human review; the post2exe message stays in the log.
TIMEOUT = "timeout"
CANNOT_HANDLE = "post2exe cannot handle it"


def review_reason(r: dict) -> str | None:
    """Human-review reason for a ``run_post2exe`` result, or None if it ran cleanly."""
    if r["stage"] == "timeout":
        return TIMEOUT
    if r["stage"] != "ran":
        return CANNOT_HANDLE
    pos, neg = r["phases"]["positive"], r["phases"]["negative"]
    if pos["unparsed"] or neg["unparsed"] or "EMPTY" in (pos["result"], neg["result"]):
        return CANNOT_HANDLE
    return None


def _unusable(r: dict) -> dict | None:
    """Result for a post2exe run that gave no usable verdict, else None."""
    if r["stage"] == "missing_testcases":
        return {"status": "error", "log": f"missing testcases: {r['detail']}"}
    if r["stage"] == "environment":
        return {"status": "error", "log": "post2exe needs tree_sitter and tree_sitter_verus "
                                          f"(post2exe/EXTERNAL_DEPS.md): {r['detail']}"}
    why = review_reason(r)
    return {"status": "unsupported", "review_reason": why, "post2exe": r} if why else None


def spec_tests(problem_id: str, program: str, testcases_root: Path, workdir: Path) -> dict:
    """``pass``/``fail`` from the test cases; ``unsupported`` (human review, with
    ``review_reason``) when post2exe cannot test this problem or specification."""
    ref = run_post2exe(problem_id, (problem_dir(problem_id) / "spec.rs").read_text(),
                       testcases_root, workdir / "reference")
    bad = _unusable(ref)
    if bad is None and {ref["phases"]["positive"]["result"], ref["phases"]["negative"]["result"]} != {"PASS"}:
        # The reference disagrees with its own test cases under post2exe.
        bad = {"status": "unsupported", "review_reason": CANNOT_HANDLE, "post2exe": ref}
    if bad:
        return {**bad, "log": "reference specification" + (f": {bad['log']}" if "log" in bad else "")}
    r = run_post2exe(problem_id, program, testcases_root, workdir / "answer")
    bad = _unusable(r)
    if bad:
        return bad
    pos, neg = r["phases"]["positive"], r["phases"]["negative"]
    ref_pos, ref_neg = ref["phases"]["positive"]["scored"], ref["phases"]["negative"]["scored"]
    if pos["result"] == "FAIL":
        return {"status": "fail", "post2exe": r, "log": f"rejects {pos['unexpected']} correct outputs"}
    if pos["scored"] < ref_pos:
        return {"status": "fail", "post2exe": r, "log": f"precondition excludes {ref_pos - pos['scored']} valid inputs"}
    if neg["result"] == "FAIL":
        return {"status": "fail", "post2exe": r, "log": f"accepts {neg['unexpected']} wrong outputs"}
    if neg["scored"] < ref_neg:
        return {"status": "fail", "post2exe": r,
                "log": f"precondition excludes inputs of {ref_neg - neg['scored']} negative cases"}
    return {"status": "pass", "post2exe": r}
