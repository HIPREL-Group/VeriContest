#!/usr/bin/env python3
"""Score Dafny solutions of VeriContest problems (End2End, Dafny version).

One solution per problem, <outputs>/<family>/<pid>.dfy. The problem's translated
spec (translator/run_all.py, --ref) fixes the entry method: its name, parameters,
result, and the contract `requires <f>_pre(..)` / `ensures <f>_post(..)`. A
Codeforces problem's entry methods are the functions its Verus starter's `main`
calls (one or two). A solution defines <f>_pre, <f>_post and each method at the
top level, and passes when every check passes, in this order:

  1. form        one file (no `include`), no `{:options}`, and each entry method's
                 header is the reference's; only a `decreases` clause may follow,
                 and only proof-search attributes (PROOF_ATTRIBUTES) may precede
                 the method's name
  2. audit       `dafny audit` has no findings: no assume, {:axiom}, {:extern},
                 {:verify false}, {:only}, declarations without a body,
                 `decreases *`, or forall statements without a body
  3. verify      `dafny verify --enforce-determinism` succeeds within LIMITS
                 (deterministic mode is what Dafny's Rust backend requires)
  4. code tests  the solution, compiled to Rust (release), reproduces every
                 expected output within the per-case limit, judged as
                 VeriContest's scorer judges (tests/checker.py where the problem
                 has one, else exact JSON, or for Codeforces the stdout as a
                 string). LeetCode: each call of the method (rust_harness.py);
                 Codeforces: each run of the program in the description, the
                 Verus starter's `main` with the methods (cf_program.py)
  5. spec tests  the solution compiled to Python: translator/dafny_driver.py
                 runs its <f>_pre / <f>_post on the testcases the reference is
                 tested on (translator/run_tests.py; for Codeforces, the calls of
                 the methods, --cf-tests-root): pre and post accept every
                 positive case and post rejects every mutated case
  6. precondition  Dafny proves the solution's <f>_pre equivalent to the
                 reference's, over the inputs the Verus parameter types can
                 represent (precondition.py). The testcases cannot show this:
                 every testcase input is valid, so a precondition that admits
                 more inputs than the reference's passes the spec tests

Spec tests need human review (SPEC_REVIEW.md) when the reference spec disagrees
with the testcases (run_tests.py's tests.jsonl in --ref), or the solution's
pre/postcondition cannot be compiled or run in time. When the reference spec
cannot be tested (it is ghost or runs out of time), a solution's spec that
passes still passes, and any other result needs review. A precondition that is
not proved equivalent needs human review too.

  python3 score.py --outputs DIR --ref DIR --vir-dir DIR --tests-root DIR [--cf-tests-root DIR] --out DIR [PID ...]

--ref may be given once per family (the translations are run per family);
--cf-tests-root (translator/run_tests.py's) is needed for Codeforces problems.
"""

import argparse
import collections
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
VERUS = os.path.join(HERE, "..", "..", "verus")        # benchmarks/verus: problems, checkers, comparison
# The translator of the reference specs is not public yet; maintainers point to it.
TRANSLATOR = os.environ.get("VERICONTEST_DAFNY_TRANSLATOR")
if not TRANSLATOR or not os.path.isfile(os.path.join(TRANSLATOR, "run_tests.py")):
    sys.exit("set VERICONTEST_DAFNY_TRANSLATOR to the translator of the reference specs; "
             "the reference specs of the Dafny version are not public yet")
sys.path.insert(0, TRANSLATOR)
import run_tests                          # noqa: E402
import vir2dafny                          # noqa: E402
from vir2dafny import L, vir              # noqa: E402
import rust_harness                       # noqa: E402
import cf_program                         # noqa: E402
import precondition                       # noqa: E402

sys.path.insert(0, os.path.join(VERUS, "evaluation"))
from vceval.checks import _outputs_match     # noqa: E402
from vceval.problems import load_checker     # noqa: E402

run_tests.BENCH = os.path.abspath(os.path.join(VERUS, "problems"))      # the Verus problems the specs come from
BENCH, DAFNY, SPEC_DRIVER = run_tests.BENCH, run_tests.DAFNY, run_tests.DRIVER
LIMITS = {
    "verify_timeout_sec": 600,            # the whole `dafny verify` run, as for Verus; no limit per task
    "audit_timeout_sec": 300,
    "build_timeout_sec": 600,             # each of `dafny build` and `cargo build --release`
    "case_timeout_sec": 1.0,              # LeetCode: one call of the entry method in the Rust build;
                                          # Codeforces: one run of the program (wall clock); as for Verus
    "code_timeout_sec": 3600,             # one run of the harness
    "spec_timeout_sec": 1800,             # all spec tests of a problem, as run_tests.py
    "precondition_time_limit_sec": 60,    # Dafny's limit per lemma of the precondition check
    "precondition_timeout_sec": 300,      # each of its two `dafny verify` runs
}
CHECKS = ("form", "audit", "verify", "code_tests", "spec_tests", "precondition")

def load_cases(path):
    """The testcases with an output."""
    with open(path) as f:
        return [c for c in (json.loads(l) for l in f if l.strip()) if "output" in c]


def run(cmd, timeout, cwd):
    try:
        r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, f"timeout after {timeout}s"
    return r.returncode, r.stdout + r.stderr


def tail(text, n=3000):
    return text if len(text) <= n else "..." + text[-n:]


# ----------------------------------------------------------------------------- form

def strip_comments(text):
    """Dafny text without comments (block comments nest); string and char literals kept."""
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("//", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
        elif text.startswith("/*", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif text[i] == "'" and not (i and (text[i - 1].isalnum() or text[i - 1] in "_'?")):
            # a char literal; after an identifier character, `'` is part of the name
            m = re.match(r"'(?:\\u\{[0-9a-fA-F]+\}|\\.|[^\\'])'", text[i:i + 16])
            j = i + (len(m.group(0)) if m else 1)
            out.append(text[i:j])
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


TOKEN = re.compile(r"[A-Za-z_?][\w'?]*|\d+|<==>|==>|<==|::|==|!=|<=|>=|&&|\|\||\.\.|:=|\S")

# Attributes that only steer proof search, which may precede the entry method's
# name (`method {:isolate_assertions} f(..)`), as a `decreases` clause may follow
# its contract. Any other attribute there changes the header.
PROOF_ATTRIBUTES = ("isolate_assertions", "vcs_split_on_every_assert", "vcs_max_cost", "vcs_max_splits",
                    "vcs_max_keep_going_splits", "resource_limit")
PROOF_ATTRIBUTE = r"\{:\s*(?:" + "|".join(PROOF_ATTRIBUTES) + r")\b[^{}]*\}"


def ref_header(spec, name):
    """The reference's `method <name>` header (signature and contract)."""
    sec = spec.split("// ===== method =====")[1]
    for block in re.split(r"(?m)^(?=method\s)", sec):
        if re.match(rf"method\s+{re.escape(name)}\s*\(", block):
            return block.strip()
    raise ValueError(f"reference has no method {name}")


def check_form(text, header):
    code = strip_comments(text)
    problems = []
    if re.search(r"(?m)^\s*include\b", code):
        problems.append("`include` is not allowed; a solution is one file")
    if "{:options" in code:
        problems.append("`{:options}` is not allowed")
    ref = TOKEN.findall(header)
    code = re.sub(rf"\bmethod\s+(?:{PROOF_ATTRIBUTE}\s*)+(?={re.escape(ref[1])}\s*[(<])", "method ", code)
    toks = TOKEN.findall(code)
    at = [i for i in range(len(toks) - 1) if toks[i] == "method" and toks[i + 1] == ref[1]]
    if len(at) != 1:
        problems.append(f"expected one `method {ref[1]}`, found {len(at)}")
    elif toks[at[0]:at[0] + len(ref)] != ref:
        problems.append(f"the entry method's header is not the reference's:\n{header}")
    else:
        rest = toks[at[0] + len(ref):]
        if rest[:1] == ["decreases"]:
            rest = rest[rest.index("{"):] if "{" in rest else []
        if rest[:1] != ["{"]:
            problems.append("only a `decreases` clause may follow the entry method's contract, then its body")
    return {"status": "fail" if problems else "pass", "problems": problems}


# ----------------------------------------------------------------------------- dafny

def audit(d):
    rc, out = run([DAFNY, "audit", "solution.dfy"], LIMITS["audit_timeout_sec"], d)
    m = re.search(r"Dafny auditor completed with (\d+) findings?", out)
    if rc != 0 or not m:
        return {"status": "fail", "log": tail(out)}
    findings = [l for l in out.splitlines() if "Possible mitigation" in l]
    return {"status": "pass" if m.group(1) == "0" else "fail", "findings": findings[:20]}


def verify(d):
    # --verification-time-limit 0: Dafny's default is 30 s per task
    rc, out = run([DAFNY, "verify", "--allow-warnings", "--enforce-determinism", "--verification-time-limit", "0",
                   "solution.dfy"], LIMITS["verify_timeout_sec"], d)
    ok = rc == 0 and re.search(r"verifier finished with \d+ verified, 0 errors", out)
    return {"status": "pass" if ok else "fail", "log": tail(out)}


def build_rust(d, binary, source):
    """Compile to Rust and build the code-test binary src/bin/<binary>.rs (release); its
    path, or None, and the log."""
    rc, out = run([DAFNY, "build", "--target:rs", "--enforce-determinism", "--no-verify", "--allow-warnings",
                   "solution.dfy", "-o", "solution"], LIMITS["build_timeout_sec"], d)
    proj = os.path.join(d, "solution-rust")
    toml = os.path.join(proj, "Cargo.toml")
    if not os.path.exists(toml):
        return None, out
    text = open(toml).read()
    if "[lib]" not in text:
        # a program with a Main method builds a binary; the harness needs the library
        with open(toml, "w") as f:
            f.write(re.sub(r'\[\[bin\]\]\nname = "solution"\npath = "src/solution.rs"',
                           '[lib]\npath = "src/solution.rs"', text))
    os.makedirs(os.path.join(proj, "src", "bin"), exist_ok=True)
    with open(os.path.join(proj, "src", "bin", f"{binary}.rs"), "w") as f:
        f.write(source)
    for _ in range(3):
        rc, cargo = run(["cargo", "build", "--release", "--offline", "--quiet"], LIMITS["build_timeout_sec"], proj)
        # parallel builds can catch the shared registry cache mid-update: retry those
        if rc == 0 or "registry" not in (cargo or ""):
            break
    exe = os.path.join(proj, "target", "release", binary)
    return (exe if rc == 0 and os.path.exists(exe) else None), out + cargo


def build(d):
    """Compile to Python; the spec tests import solution-py/module_.py."""
    rc, out = run([DAFNY, "build", "--target:py", "--no-verify", "--allow-warnings", "solution.dfy",
                   "-o", "solution"], LIMITS["build_timeout_sec"], d)
    return os.path.exists(os.path.join(d, "solution-py", "module_.py")), out


# ----------------------------------------------------------------------------- tests

def signatures(rec, args):
    fam, pid = rec["family"], rec["problem"]
    items = vir.parse(open(os.path.join(args.vir_dir, f"{fam}__{pid}", "log", "crate.vir")).read())
    targets = L.target_names(os.path.join(BENCH, fam, pid, "spec.rs"))
    fixes = {k: set(v) for k, v in (rec.get("fixes") or {}).items()}
    return vir2dafny.Translator(items, targets, fixes).translate()["signatures"]


def reference_sig(rec, args):
    """The entry method's signature, as run_tests.run_problem selects it for LeetCode."""
    return run_tests.entry(rec["family"], rec["problem"], signatures(rec, args), args.tests_root)


def entry_sigs(rec, args):
    """The entry methods' signatures: a LeetCode problem's one, or the functions a
    Codeforces starter's `main` calls (run_tests.cf_entries, with their Rust names).
    None if that does not tell."""
    if rec["family"] == "leetcode":
        sig = reference_sig(rec, args)
        return [sig] if sig else None
    return run_tests.cf_entries(rec["problem"], signatures(rec, args))


def driver(script, d, cases_json, *extra, timeout):
    # as run_tests.py: deep recursion in compiled Dafny needs the stack
    cmd = f"ulimit -s unlimited 2>/dev/null; exec python3 {script} solution-py {cases_json} {' '.join(extra)}"
    try:
        r = subprocess.run(["bash", "-c", cmd], cwd=d, capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return None, f"timeout after {timeout}s"


def run_harness(exe, d):
    try:
        r = subprocess.run([exe, "code_cases.txt", "code.jsonl", str(LIMITS["case_timeout_sec"])], cwd=d,
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True, errors="replace",
                           timeout=LIMITS["code_timeout_sec"])
        return r.returncode, r.stderr
    except subprocess.TimeoutExpired:
        return None, f"timeout after {LIMITS['code_timeout_sec']}s"


def code_tests(fam, pid, sig, exe, d, args):
    cases = load_cases(os.path.join(args.tests_root, fam, pid, "tests", "testcases.jsonl"))
    results, lines, crashes, log = {}, {}, 0, ""
    for i, c in enumerate(cases):
        try:
            lines[i] = rust_harness.case_line(i, sig, c["input"], run_tests.norm)
        except rust_harness.IllTyped as e:
            results[i] = {"case": i, "status": "ill_typed", "detail": str(e)}
    while True:
        todo = [i for i in lines if i not in results]
        if not todo:
            break
        with open(os.path.join(d, "code_cases.txt"), "w") as f:
            f.write("\n".join(lines[i] for i in todo) + "\n")
        rc, err = run_harness(exe, d)
        before = len(results)
        if os.path.exists(os.path.join(d, "code.jsonl")):
            with open(os.path.join(d, "code.jsonl")) as f:
                for r in map(json.loads, f):
                    results[r["case"]] = r
        if rc is None:      # out of time for the whole problem
            for i in todo:
                results.setdefault(i, {"case": i, "status": "timeout"})
        elif rc == rust_harness.EXIT_TIMEOUT:      # stopped after a case that ran past its limit
            continue
        elif rc != 0 or len(results) == before:     # the first case without a result killed the harness
            log = tail(err, 1500)
            first = next((i for i in todo if i not in results), None)
            if first is None:
                break
            results[first] = {"case": first, "status": "runtime_error", "detail": f"harness died ({rc}): " + err[-300:]}
            crashes += 1
            if crashes > 20:
                for i in todo:
                    results.setdefault(i, {"case": i, "status": "runtime_error", "detail": "not run: harness died 20 times"})
    checker = load_checker(f"{fam}/{pid}")
    passed, counts, failures, ill_typed = 0, collections.Counter(), [], []
    for i, c in enumerate(cases):
        r = results[i]
        counts[r["status"]] += 1
        if r["status"] == "ill_typed":          # the testcase does not fit the reference signature
            ill_typed.append(i)
            continue
        if r["status"] != "ok":
            failures.append({"case": i, "reason": r["status"], "detail": r.get("detail", "")})
            continue
        actual = r["output"]       # with several outputs, already {"nums": .., "return": ..}
        if pid in run_tests.WRAPPERS:      # the testcases give the Verus starter's wrapper's result
            actual = run_tests.WRAPPERS[pid]["from_entry"](c["input"], actual)
        if sig["mut"] and isinstance(c["output"], dict):
            # a `&mut` parameter: the harness prints its final value under its name
            k = next((k for k in c["output"] if run_tests.norm(k) == run_tests.norm(sig["mut"])), sig["mut"])
            actual = {k: actual}
        if checker is not None:
            try:
                ok = bool(checker(c["input"], actual))
            except Exception:
                ok = False
        else:
            ok = _outputs_match(c["output"], actual)
        if ok:
            passed += 1
        else:
            failures.append({"case": i, "expected": c["output"], "actual": actual})
    times = [r["time"] for r in results.values() if r["status"] == "ok"]
    total = len(cases)
    status = "error" if ill_typed else ("pass" if total and passed == total else "fail")
    short = [{k: (v if len(json.dumps(v)) <= 300 else json.dumps(v)[:300] + "...") for k, v in f.items()}
             for f in failures[:5]]
    return {"status": status, "passed": passed, "total": total, "statuses": dict(counts),
            "max_case_time": max(times, default=None), "judge": "checker" if checker else "exact",
            "ill_typed_cases": ill_typed[:10], "failed_cases": short, **({"log": log} if log else {})}


def code_tests_cf(pid, exe, args):
    """Runs the program (cf_program.py) on each testcase's stdin, as VeriContest's
    scorer runs main.rs: the wall clock of each run within the per-case limit, and
    the stdout judged by tests/checker.py where the problem has one, else compared
    with the expected one as a string."""
    cases = load_cases(os.path.join(args.tests_root, "codeforces", pid, "tests", "testcases.jsonl"))
    checker = load_checker(f"codeforces/{pid}")
    deadline = time.monotonic() + LIMITS["code_timeout_sec"]
    passed, counts, failures, times = 0, collections.Counter(), [], []
    for i, c in enumerate(cases):
        if time.monotonic() > deadline:
            counts["not_run"] += 1
            failures.append({"case": i, "reason": "not run: out of time for the problem"})
            continue
        t0 = time.monotonic()
        try:
            r = subprocess.run([exe], input=c["input"], capture_output=True, text=True, errors="replace",
                               timeout=LIMITS["case_timeout_sec"])
        except subprocess.TimeoutExpired:
            counts["timeout"] += 1
            failures.append({"case": i, "reason": "timeout"})
            continue
        secs = time.monotonic() - t0
        if r.returncode != 0:
            counts["runtime_error"] += 1
            failures.append({"case": i, "reason": "runtime_error", "detail": r.stderr[-300:]})
            continue
        counts["ok"] += 1
        times.append(secs)
        if checker is not None:
            try:
                ok = bool(checker(c["input"], r.stdout))
            except Exception:
                ok = False
        else:
            ok = _outputs_match(c["output"], r.stdout)
        if ok:
            passed += 1
        else:
            failures.append({"case": i, "expected": c["output"], "actual": r.stdout})
    short = [{k: (v if len(json.dumps(v)) <= 300 else json.dumps(v)[:300] + "...") for k, v in f.items()}
             for f in failures[:5]]
    total = len(cases)
    return {"status": "pass" if total and passed == total else "fail", "passed": passed,
            "total": total, "statuses": dict(counts), "max_case_time": max(times, default=None),
            "judge": "checker" if checker else "exact", "failed_cases": short}


# run_tests.py statuses of a reference spec that ran and disagrees with its testcases
REF_DISAGREES = ("fail", "invalid_testcases")


def spec_tests(fam, pid, sigs, ref_status, d, args):
    if ref_status in REF_DISAGREES:
        return {"status": "review", "reason": f"the reference spec disagrees with the testcases ({ref_status})"}
    cases = run_tests.problem_cases(fam, pid, sigs, args)
    if cases is None:
        if fam == "codeforces":     # cf_harness.py could not decode the stdout into results
            return {"status": "review", "reason": "no function-level testcases"}
        return {"status": "error", "reason": "no testcases"}
    data, stats = run_tests.select(sigs, cases, args.spec_max_size)
    with open(os.path.join(d, "spec_cases.json"), "w") as f:
        json.dump(data, f)
    rc, out = driver(SPEC_DRIVER, d, "spec_cases.json", timeout=LIMITS["spec_timeout_sec"])
    if rc is None:
        return {"status": "review", "reason": "timeout", **stats}
    if "compiled spec has no" in out:
        return {"status": "review", "reason": "the pre/postcondition is not compilable", "log": tail(out, 500)}
    try:
        res = json.loads(out.strip().splitlines()[-1])
    except (IndexError, json.JSONDecodeError):
        return {"status": "review", "reason": "the spec could not be run", "log": tail(out, 1500)}
    pos, neg = res["pos"], res["neg"]
    if pos["failed"] or neg["failed"] or pos["pre_rejected"]:
        status, reason = "fail", None
    elif pos["timed_out"] or neg["timed_out"] or pos["skipped"] or neg["skipped"]:
        status, reason = "review", "timeout"
    elif pos["errors"] or neg["errors"]:
        status, reason = "review", "the spec raised errors on some testcases"
    elif not pos["checked"]:
        status, reason = "review", "no testcase small enough"
    else:
        status, reason = "pass", None
    if ref_status != "pass" and status != "pass":
        # the testcases were not checked against the reference: a rejected input may be outside its precondition
        status, reason = "review", f"the reference spec cannot be tested ({ref_status}); " + (
            "the spec fails the spec tests" if status == "fail" else reason)
    return {"status": status, **({"reason": reason} if reason else {}), **stats, "spec-pos": pos, "spec-neg": neg}


def precondition_check(text, spec, sigs, d):
    """precondition.check for each entry method: pass if every one is proved, error if
    one could not be checked, else review."""
    res = {s["name"]: precondition.check(DAFNY, text, spec, s["name"], os.path.join(d, "precondition", str(i)),
                                         LIMITS["precondition_time_limit_sec"], LIMITS["precondition_timeout_sec"])
           for i, s in enumerate(sigs)}
    if len(res) == 1:
        return next(iter(res.values()))
    sts = [r["status"] for r in res.values()]
    status = "error" if "error" in sts else ("pass" if all(x == "pass" for x in sts) else "review")
    reasons = [f"{n}: {r['reason']}" for n, r in res.items() if r.get("reason")]
    return {"status": status, **({"reason": "; ".join(reasons)} if reasons else {}), "methods": res}


# ----------------------------------------------------------------------------- driver

def score_problem(rec, ref_tests, args):
    fam, pid = rec["family"], rec["problem"]
    checks = {c: "not_run" for c in CHECKS}
    log = {"problem_id": f"{fam}/{pid}"}

    def done(status, notes=""):
        os.makedirs(os.path.join(args.out, "eval_logs", fam), exist_ok=True)
        with open(os.path.join(args.out, "eval_logs", fam, f"{pid}.json"), "w") as f:
            json.dump(log, f, indent=1)
        return {"problem_id": f"{fam}/{pid}", "status": status, "checks": checks, "notes": notes,
                "log": f"eval_logs/{fam}/{pid}.json"}

    path = os.path.join(args.outputs, fam, f"{pid}.dfy")
    if not os.path.exists(path):
        return done("fail", "no solution")
    text = open(path).read()
    sigs = entry_sigs(rec, args)
    if not sigs:
        return done("error", "cannot tell which contract the testcases are for")
    spec = open(os.path.join(rec["ref_dir"], fam, pid, "spec.dfy")).read()
    forms = [check_form(text, ref_header(spec, s["name"])) for s in sigs]
    log["form"] = {"status": "fail" if any(f["status"] != "pass" for f in forms) else "pass",
                   "problems": [p for f in forms for p in f["problems"]]}
    checks["form"] = log["form"]["status"]
    if checks["form"] != "pass":
        return done("fail", "; ".join(log["form"]["problems"]))
    with tempfile.TemporaryDirectory() as d:
        with open(os.path.join(d, "solution.dfy"), "w") as f:
            f.write(text)
        for name, step in (("audit", audit), ("verify", verify)):
            log[name] = step(d)
            checks[name] = log[name]["status"]
            if checks[name] != "pass":
                return done("fail", f"{name} failed")
        try:
            if fam == "leetcode":
                exe, out = build_rust(d, "harness", rust_harness.source(sigs[0]))
            else:
                main_rs = open(os.path.join(BENCH, fam, pid, "main.rs")).read()
                exe, out = build_rust(d, "cfmain", cf_program.source(main_rs, sigs, run_tests.cf_harness.signature))
        except rust_harness.IllTyped as e:      # a signature type the harness cannot convert
            checks["code_tests"] = "error"
            log["code_tests"] = {"status": "error", "log": str(e)}
            return done("error", f"code tests: {e}")
        if exe is None:
            checks["code_tests"] = "fail"
            log["code_tests"] = {"status": "fail", "log": "Rust build failed\n" + tail(out)}
            return done("fail", "Rust build failed")
        log["code_tests"] = (code_tests(fam, pid, sigs[0], exe, d, args) if fam == "leetcode"
                             else code_tests_cf(pid, exe, args))
        checks["code_tests"] = log["code_tests"]["status"]
        if checks["code_tests"] != "pass":
            return done("error" if checks["code_tests"] == "error" else "fail", "code tests did not pass")
        ok, out = build(d)
        if ok:
            log["spec_tests"] = spec_tests(fam, pid, sigs, ref_tests.get(pid, "not tested"), d, args)
        else:
            log["spec_tests"] = {"status": "review", "reason": "Python build failed", "log": tail(out)}
        checks["spec_tests"] = log["spec_tests"]["status"]
        if checks["spec_tests"] in ("pass", "review"):
            log["precondition"] = precondition_check(text, spec, sigs, d)
            checks["precondition"] = log["precondition"]["status"]
    st, pre = checks["spec_tests"], checks["precondition"]
    if st == "fail":
        return done("fail", log["spec_tests"].get("reason") or "")
    if st not in ("pass", "review") or pre == "error":
        return done("error", log["spec_tests"].get("reason") or log.get("precondition", {}).get("reason", ""))
    reasons = [r for r in (log["spec_tests"].get("reason") if st == "review" else None,
                           log["precondition"].get("reason") if pre == "review" else None) if r]
    return done("pass" if st == "pass" and pre == "pass" else "review", "; ".join(reasons))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("problems", nargs="*", help="problem ids (default: every problem of --ref translated ok)")
    ap.add_argument("--outputs", required=True, help="solutions, DIR/<family>/<pid>.dfy")
    ap.add_argument("--ref", required=True, action="append",
                    help="output of translator/run_all.py and run_tests.py; may be given once per family")
    ap.add_argument("--vir-dir", required=True)
    ap.add_argument("--tests-root", required=True, help="DIR/<family>/<pid>/tests/{testcases,mutated_testcases}.jsonl")
    ap.add_argument("--cf-tests-root", help="function-level Codeforces testcases, as for run_tests.py")
    ap.add_argument("--out", required=True)
    ap.add_argument("--spec-max-size", type=int, default=50, help="as run_tests.py (must match the reference run)")
    ap.add_argument("--case-timeout", type=float, default=LIMITS["case_timeout_sec"],
                    help="seconds per call of the compiled method (default %(default)s)")
    ap.add_argument("--jobs", type=int, default=8)
    args = ap.parse_args()
    LIMITS["case_timeout_sec"] = args.case_timeout
    recs, ref_tests = [], {}
    for ref in args.ref:
        recs += [dict(r, ref_dir=ref) for r in map(json.loads, open(os.path.join(ref, "report.jsonl")))]
        tests_path = os.path.join(ref, "tests.jsonl")
        if os.path.exists(tests_path):
            ref_tests.update({r["problem"]: r["status"] for r in map(json.loads, open(tests_path))})
    recs = [r for r in recs if r["status"] == "ok" and (not args.problems or r["problem"] in args.problems)]
    if any(r["family"] == "codeforces" for r in recs) and not args.cf_tests_root:
        ap.error("Codeforces problems need --cf-tests-root")
    os.makedirs(args.out, exist_ok=True)

    def one(rec):
        try:
            return score_problem(rec, ref_tests, args)
        except Exception as e:
            return {"problem_id": f"{rec['family']}/{rec['problem']}", "status": "error",
                    "checks": {}, "notes": f"scorer error: {type(e).__name__}: {e}"}

    results = []
    with ThreadPoolExecutor(args.jobs) as ex:
        for r in ex.map(one, recs):
            results.append(r)
            print(r["problem_id"], r["status"], r["checks"], r["notes"][:150], flush=True)
    with open(os.path.join(args.out, "results.jsonl"), "w") as f:
        for r in results:
            f.write(json.dumps(r) + "\n")
    c = collections.Counter(r["status"] for r in results)
    _, version = run([DAFNY, "--version"], 60, HERE)
    summary = {"problems": len(results), "counts": dict(c),
               "automatic_pass_rate": c["pass"] / len(results) if results else None,
               "spec_review_problem_ids": [r["problem_id"] for r in results if r["status"] == "review"],
               "precondition_review_problem_ids": [r["problem_id"] for r in results
                                                   if r.get("checks", {}).get("precondition") == "review"],
               "dafny_version": version.strip(), "limits": LIMITS, "spec_max_size": args.spec_max_size}
    with open(os.path.join(args.out, "summary.json"), "w") as f:
        json.dump(summary, f, indent=1)
    print(dict(c))


if __name__ == "__main__":
    main()
