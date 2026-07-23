"""Execution driver: compile code.rs/main.rs into a runnable program.

For LeetCode we synthesize a main() that reads one JSON case on stdin, calls
Solution::<fn>, and prints the output as JSON. For Codeforces main.rs is already
a complete stdin->stdout program and is used verbatim.

Environments without a native linker (no MSVC/mingw) cannot produce a runnable
binary. build_driver still type-checks the generated Rust via `rustc
--emit=metadata` (validates codegen), records build_ok=False, and callers gate
execution on DriverBuild.build_ok.
"""
from __future__ import annotations

import json
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path

from spec_testing.common.config import get
from spec_testing.common.repo import Problem
from spec_testing.common.specmodel import SpecModel, GenError, load_spec_model
from .codegen import build_lc_main, build_cf_capture_main


@dataclass
class DriverBuild:
    problem_id: str
    exe: Path | None
    src: Path
    typecheck_ok: bool
    build_ok: bool
    error: str = ""


def _rustc() -> str | None:
    cfg = get("paths", "rustc_bin", "auto")
    if cfg and cfg != "auto" and Path(cfg).exists():
        return cfg
    return shutil.which("rustc")


_LINKER_OK: bool | None = None


def linker_available() -> bool:
    """One-time probe: can rustc link a native binary in this environment?
    Cached so full-dataset runs skip the doomed link step per problem."""
    global _LINKER_OK
    if _LINKER_OK is not None:
        return _LINKER_OK
    rustc = _rustc()
    if rustc is None:
        _LINKER_OK = False
        return False
    import tempfile
    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "probe.rs"
        src.write_text("fn main() { println!(\"ok\"); }", encoding="utf-8")
        exe = Path(td) / "probe.exe"
        try:
            r = subprocess.run([rustc, "-O", "-o", str(exe), str(src)],
                               capture_output=True, text=True, timeout=60)
            _LINKER_OK = (r.returncode == 0 and exe.exists())
        except (OSError, subprocess.SubprocessError):
            _LINKER_OK = False
    return _LINKER_OK


def _driver_source(problem: Problem, model: SpecModel | None) -> str | None:
    if problem.is_codeforces:
        return problem.read("main.rs")
    code = problem.read("code.rs")
    if code is None or model is None:
        return None
    return build_lc_main(code, model)


def build_driver(problem: Problem, workdir: Path, model: SpecModel | None = None) -> DriverBuild:
    workdir.mkdir(parents=True, exist_ok=True)
    if model is None and not problem.is_codeforces:
        m = load_spec_model(problem)
        model = None if isinstance(m, GenError) else m
    src_text = _driver_source(problem, model)
    src = workdir / "main.rs"
    if src_text is None:
        return DriverBuild(problem.problem_id, None, src, False, False, "no driver source")
    src.write_text(src_text, encoding="utf-8")

    rustc = _rustc()
    if rustc is None:
        return DriverBuild(problem.problem_id, None, src, False, False, "rustc not found")

    build_timeout = int(get("testgen", "build_timeout_s", 60))

    # 1) type-check only (no linker needed) — validates codegen.
    meta = workdir / "main.meta"
    tc = subprocess.run(
        [rustc, "--edition=2021", "--emit=metadata", "--crate-type=bin",
         "-o", str(meta), str(src)],
        capture_output=True, text=True, timeout=build_timeout,
        encoding="utf-8", errors="replace",
    )
    typecheck_ok = tc.returncode == 0
    if not typecheck_ok:
        return DriverBuild(problem.problem_id, None, src, False, False,
                           _first_error(tc.stderr))

    # 2) full build (needs linker). Skip the doomed step in linker-less envs.
    if not linker_available():
        return DriverBuild(problem.problem_id, None, src, True, False, "no native linker")
    exe = workdir / ("driver.exe")
    fb = subprocess.run(
        [rustc, "-O", "--edition=2021", "-o", str(exe), str(src)],
        capture_output=True, text=True, timeout=build_timeout,
        encoding="utf-8", errors="replace",
    )
    build_ok = fb.returncode == 0 and exe.exists()
    err = "" if build_ok else _first_error(fb.stderr)
    return DriverBuild(problem.problem_id, exe if build_ok else None, src,
                       typecheck_ok, build_ok, err)


_CAPTURE_TAG = "__CAPTURE__"


def build_capture_driver(problem: Problem, workdir: Path, model: SpecModel,
                         main_override: str | None = None) -> DriverBuild:
    """Codeforces only: build a driver whose main() is instrumented to emit the
    exact typed (input, output) each `Solution::<fn>` call receives — ground
    truth, no heuristic stdin/stdout parsing (see codegen.build_cf_capture_main).

    `main_override` supplies alternative main.rs source (e.g. a code mutant);
    otherwise the problem's own main.rs is used."""
    workdir.mkdir(parents=True, exist_ok=True)
    main_rs = main_override if main_override is not None else problem.read("main.rs")
    src = workdir / "main.rs"
    if not problem.is_codeforces or main_rs is None or model is None:
        return DriverBuild(problem.problem_id, None, src, False, False, "no capture source")
    src.write_text(build_cf_capture_main(main_rs, model), encoding="utf-8")

    rustc = _rustc()
    if rustc is None:
        return DriverBuild(problem.problem_id, None, src, False, False, "rustc not found")
    build_timeout = int(get("testgen", "build_timeout_s", 60))
    meta = workdir / "main.meta"
    tc = subprocess.run(
        [rustc, "--edition=2021", "--emit=metadata", "--crate-type=bin", "-o", str(meta), str(src)],
        capture_output=True, text=True, timeout=build_timeout, encoding="utf-8", errors="replace")
    if tc.returncode != 0:
        return DriverBuild(problem.problem_id, None, src, False, False, _first_error(tc.stderr))
    if not linker_available():
        return DriverBuild(problem.problem_id, None, src, True, False, "no native linker")
    exe = workdir / "capture.exe"
    fb = subprocess.run(
        [rustc, "-O", "--edition=2021", "-o", str(exe), str(src)],
        capture_output=True, text=True, timeout=build_timeout, encoding="utf-8", errors="replace")
    build_ok = fb.returncode == 0 and exe.exists()
    return DriverBuild(problem.problem_id, exe if build_ok else None, src,
                       True, build_ok, "" if build_ok else _first_error(fb.stderr))


def _norm_ws(s: str) -> str:
    """Whitespace-normalized token stream, for comparing CF stdout to the
    expected answer regardless of spacing/blank-line differences."""
    return " ".join(s.split())


def capture_seed_pairs(build: DriverBuild, problem: Problem) -> list[dict]:
    """Ground-truth Codeforces seeds from an already-built capture driver: feed
    each raw description-example stdin and collect the captured typed
    {"input": <dict>, "output": <value>, "authoritative": <bool>} pairs (one per
    Solution::<fn> call). `authoritative` is True when the driver's own stdout
    reproduces the example's expected output verbatim — i.e. the reference is
    confirmed correct for that example, so the captured pair is problem-statement
    ground truth (not merely what the reference happened to compute). Empty if the
    driver isn't runnable or no examples parse."""
    from spec_testing.testgen import seeds as seeds_mod
    if not build.build_ok:
        return []
    raw = seeds_mod._extract_cf(problem.read("description.md") or "")
    if not raw.ok:
        return []
    pairs: list[dict] = []
    for s in raw.seeds:
        captured, stdout = run_capture_full(build, str(s.input))
        authoritative = _norm_ws(stdout) == _norm_ws(str(s.output))
        for pair in captured:
            if (isinstance(pair, dict) and isinstance(pair.get("input"), dict)
                    and "output" in pair):
                pair["authoritative"] = authoritative
                pairs.append(pair)
    return pairs


def capture_seeds(problem: Problem, model: SpecModel, workdir: Path) -> list[dict]:
    """Convenience: build the capture driver in `workdir` and return its
    ground-truth seed pairs (see capture_seed_pairs)."""
    if not problem.is_codeforces or model is None:
        return []
    return capture_seed_pairs(build_capture_driver(problem, workdir, model), problem)


def run_capture_full(build: DriverBuild, stdin_text: str,
                     timeout_s: int | None = None) -> tuple[list[dict], str]:
    """Feed raw CF stdin to a capture driver; return (captured pairs, stdout).
    Each pair is {"input": <dict>, "output": <value>}, one per Solution::<fn>
    call (a multi-test-case stdin yields one pair per case). stdout is the real
    CF answer stream. Returns ([], "") on any failure."""
    if not build.build_ok or build.exe is None:
        return [], ""
    if timeout_s is None:
        timeout_s = int(get("testgen", "drv_timeout_s", 10))
    try:
        proc = subprocess.run([str(build.exe)], input=stdin_text, capture_output=True,
                              text=True, timeout=timeout_s, encoding="utf-8", errors="replace")
    except (subprocess.SubprocessError, OSError):
        return [], ""
    pairs: list[dict] = []
    for line in proc.stderr.splitlines():
        if line.startswith(_CAPTURE_TAG):
            try:
                pairs.append(json.loads(line[len(_CAPTURE_TAG):]))
            except json.JSONDecodeError:
                continue
    return pairs, proc.stdout


def run_capture(build: DriverBuild, stdin_text: str, timeout_s: int | None = None) -> list[dict]:
    """Captured (input, output) pairs only — see run_capture_full."""
    return run_capture_full(build, stdin_text, timeout_s)[0]


def _first_error(stderr: str) -> str:
    for line in stderr.splitlines():
        if "error" in line.lower():
            return line.strip()[:300]
    return stderr.strip()[:300]


@dataclass
class RunResult:
    ok: bool
    output: object            # decoded JSON (LC) or raw stdout str (CF)
    stdout: str = ""
    error: str = ""


def run_case(build: DriverBuild, problem: Problem, case_input, timeout_s: int | None = None,
             model: SpecModel | None = None) -> RunResult:
    """Run the built driver on one input. Requires build.build_ok."""
    if not build.build_ok or build.exe is None:
        return RunResult(False, None, error="driver not built (no linker)")
    if timeout_s is None:
        timeout_s = int(get("testgen", "drv_timeout_s", 10))

    from spec_testing.common import cf_io
    use_cf_io = problem.is_codeforces and isinstance(case_input, dict)
    if use_cf_io and model is None:
        m = load_spec_model(problem)
        model = None if isinstance(m, GenError) else m

    if use_cf_io and model is not None:
        try:
            stdin_text = cf_io.build_stdin_generic(model, case_input)
        except Exception as exc:
            return RunResult(False, None, error=f"build_stdin: {exc}")
    elif problem.is_codeforces:
        stdin_text = case_input if isinstance(case_input, str) else str(case_input)
    else:
        stdin_text = json.dumps({"input": case_input})

    try:
        proc = subprocess.run(
            [str(build.exe)], input=stdin_text, capture_output=True, text=True,
            timeout=timeout_s, encoding="utf-8", errors="replace",
        )
    except subprocess.TimeoutExpired:
        return RunResult(False, None, error="timeout")
    except OSError as exc:
        return RunResult(False, None, error=f"exec: {exc}")
    if proc.returncode != 0:
        return RunResult(False, None, stdout=proc.stdout, error=f"exit {proc.returncode}: {proc.stderr[:200]}")

    out_text = proc.stdout.strip()
    if use_cf_io and model is not None:
        parsed = cf_io.parse_stdout_generic(model, out_text)
        if parsed is None:
            return RunResult(False, None, stdout=proc.stdout, error="unparseable CF stdout")
        return RunResult(True, parsed, stdout=proc.stdout)


    if problem.is_codeforces:
        return RunResult(True, out_text, stdout=proc.stdout)
    try:
        return RunResult(True, json.loads(out_text), stdout=proc.stdout)
    except json.JSONDecodeError:
        return RunResult(False, None, stdout=proc.stdout, error="non-JSON output")

