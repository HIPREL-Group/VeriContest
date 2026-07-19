#!/usr/bin/env python3
"""Compile and run test input generators.

Run from the repository root (paths are relative to the repo):

    python3 test_gen/run_generators.py                    # Run all generators
    python3 test_gen/run_generators.py lc1 lc231 lc704    # Run specific generators
    python3 test_gen/run_generators.py -j 8               # Run with 8 parallel workers
    python3 test_gen/run_generators.py --list              # List available generators

Each generator writes ``tests/testcases.jsonl`` next to ``tests/gen.rs``.

Compilation uses ``--compile-timeout`` (default 60s). Running the generator (which
executes ``code.rs`` to produce outputs) uses ``--run-timeout`` (default 600s).
Pass ``--timeout SEC`` to use the same limit for both steps.

Failures are appended as JSON lines to ``test_gen/gen_pipeline_errors.jsonl``
(same format as ``gen_testcases.py``). Override with env ``GEN_PIPELINE_ERROR_LOG``.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

# This file lives at test_gen/run_generators.py
REPO_ROOT = Path(__file__).resolve().parent.parent
_TEST_GEN_DIR = Path(__file__).resolve().parent
if str(_TEST_GEN_DIR) not in sys.path:
    sys.path.insert(0, str(_TEST_GEN_DIR))
from build_harness import compile_cf_main_bin  # noqa: E402

# Support crate whose only job is to vendor serde/serde_json as compiled rlibs,
# so Verus can link them with --extern when it compiles each tests/gen.rs.
VERUS_DEPS_DIR = _TEST_GEN_DIR / "verus_deps"
DEPS_DIR = VERUS_DEPS_DIR / "target" / "debug" / "deps"
_DEFAULT_PIPELINE_ERROR_LOG = REPO_ROOT / "test_gen" / "gen_pipeline_errors.jsonl"

COMMAND_NAME = "run-generators"


def append_pipeline_error(
    problem_id: str,
    stage: str,
    detail: str,
    *,
    extra: dict[str, Any] | None = None,
) -> None:
    """Append one JSON line (same schema as ``gen_testcases.append_pipeline_error``).

    Uses ``fcntl.flock`` when available so parallel workers do not corrupt the file.
    """
    path = Path(os.environ.get("GEN_PIPELINE_ERROR_LOG", str(_DEFAULT_PIPELINE_ERROR_LOG)))
    rec: dict[str, Any] = {
        "ts": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "command": COMMAND_NAME,
        "problem_id": problem_id,
        "stage": stage,
        "detail": (detail or "")[:32000],
    }
    if extra:
        rec["extra"] = extra
    line = json.dumps(rec, ensure_ascii=False) + "\n"
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        try:
            import fcntl
        except ImportError:
            fcntl = None  # type: ignore[assignment]
        with open(path, "a", encoding="utf-8") as f:
            if fcntl is not None:
                fcntl.flock(f.fileno(), fcntl.LOCK_EX)
            try:
                f.write(line)
                f.flush()
            finally:
                if fcntl is not None:
                    fcntl.flock(f.fileno(), fcntl.LOCK_UN)
    except OSError as e:
        print(f"[append_pipeline_error] could not write {path}: {e}", file=sys.stderr)

DEFAULT_COMPILE_TIMEOUT = 60  # Verus ``--compile`` for gen.rs
DEFAULT_RUN_TIMEOUT = 600  # generator binary; runs ``code.rs`` for each case

# After a Codeforces generator writes ``testcases.jsonl``, verify ``main.rs`` I/O
# for problems listed in ``cf_batch4_stdio.py`` (no extra JSONL keys).
_CF_STDIO_SCRIPT = REPO_ROOT / "test_gen" / "cf_batch4_stdio.py"


def _verify_cf_stdio_jsonl(problem_id: str) -> None:
    if not problem_id.startswith("cf") or not _CF_STDIO_SCRIPT.is_file():
        return
    try:
        r = subprocess.run(
            [sys.executable, str(_CF_STDIO_SCRIPT), "--problem", problem_id],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=300,
        )
    except subprocess.TimeoutExpired:
        print(f"  ⚠️  {problem_id}: cf_batch4_stdio.py timed out", file=sys.stderr)
        return
    if r.returncode != 0:
        msg = (r.stderr or r.stdout or "").strip()[:500]
        if msg and "skip" not in msg.lower():
            print(f"  ⚠️  {problem_id}: main.rs verify (cf_batch4_stdio): {msg}", file=sys.stderr)


def verus_binary() -> str:
    """Resolve Verus executable: ``VERUS`` env, then ``<repo>/verus/verus``, then ``PATH``."""
    env = os.environ.get("VERUS")
    if env and Path(env).is_file():
        return env
    bundled = REPO_ROOT / "verus" / "verus"
    if bundled.is_file():
        return str(bundled)
    which = shutil.which("verus")
    if which:
        return which
    return "verus"


def find_all_generators() -> list[Path]:
    """Find all tests/gen.rs files."""
    patterns = [
        "benchmark/leetcode/*/tests/gen.rs",
        "benchmark/codeforces/*/tests/gen.rs",
    ]
    results = []
    for pattern in patterns:
        results.extend(sorted(REPO_ROOT.glob(pattern)))
    return results


def problem_name(gen_path: Path) -> str:
    """Extract problem name (e.g., 'lc1') from gen.rs path."""
    return gen_path.parent.parent.name


def build_deps() -> bool:
    """Build serde_json dependencies via cargo."""
    cargo_toml = VERUS_DEPS_DIR / "Cargo.toml"
    if not cargo_toml.is_file():
        msg = (
            f"Missing {cargo_toml}.\n"
            "Create the `test_gen/verus_deps` crate (serde + serde_json) so Verus can link "
            "`--extern serde` / `--extern serde_json` when compiling `tests/gen.rs`. "
            "See test_gen/README.md (Requirements)."
        )
        print(f"  ❌ {msg}", file=sys.stderr)
        append_pipeline_error(
            "_verus_deps",
            "verus_deps_missing",
            msg,
            extra={"cargo_toml": str(cargo_toml)},
        )
        return False
    print("Building serde_json dependencies...")
    result = subprocess.run(
        ["cargo", "build"],
        cwd=VERUS_DEPS_DIR,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        err = (result.stderr or result.stdout or "").strip()
        print(f"  ❌ cargo build failed:\n{result.stderr}", file=sys.stderr)
        append_pipeline_error(
            "_verus_deps",
            "cargo_build_deps",
            err or "cargo build failed with no stderr",
            extra={"cwd": str(VERUS_DEPS_DIR), "returncode": result.returncode},
        )
        return False
    print("  ✅ Dependencies built")
    return True


def find_rlib(pattern: str) -> str | None:
    """Find an rlib file matching a glob pattern in the deps directory."""
    matches = glob.glob(str(DEPS_DIR / pattern))
    if not matches:
        return None
    return matches[0]


def compile_generator(gen_path: Path, binary: Path | None = None,
                      timeout: int = DEFAULT_COMPILE_TIMEOUT) -> Path | None | str:
    """Compile a generator with Verus.

    Returns the binary path on success, None on failure, or ``"timeout"``
    if compilation exceeded the time limit.
    """
    name = problem_name(gen_path)
    if binary is None:
        binary = gen_path.parent / "gen"

    serde_json = find_rlib("libserde_json-*.rlib")
    serde = find_rlib("libserde-*.rlib")
    if not serde_json or not serde:
        detail = f"serde rlibs not found in {DEPS_DIR}"
        print(f"  ❌ {name}: {detail}")
        append_pipeline_error(
            name,
            "serde_rlibs_missing",
            detail,
            extra={"gen_rs": str(gen_path), "deps_dir": str(DEPS_DIR)},
        )
        return None

    vb = verus_binary()
    cmd = [
        vb, "--compile",
        "--rlimit", "300000",
        str(gen_path),
        "-L", f"dependency={DEPS_DIR}",
        "--extern", f"serde_json={serde_json}",
        "--extern", f"serde={serde}",
        "-o", str(binary),
    ]

    try:
        result = subprocess.run(
            cmd,
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        print(f"  ⏰ {name}: compilation timed out ({timeout}s)")
        append_pipeline_error(
            name,
            "verus_compile_timeout",
            f"Verus --compile timed out after {timeout}s",
            extra={"gen_rs": str(gen_path)},
        )
        return "timeout"

    if result.returncode != 0 or "errors" in result.stderr and "0 errors" not in result.stderr:
        # Check for verification errors in combined output
        output = result.stdout + result.stderr
        if "0 errors" not in output:
            print(f"  ❌ {name}: compilation/verification failed")
            for line in output.splitlines():
                if "error" in line.lower() or "verification" in line.lower():
                    print(f"     {line}")
            append_pipeline_error(
                name,
                "verus_compile_failed",
                output.strip() or "compilation failed with empty output",
                extra={
                    "gen_rs": str(gen_path),
                    "returncode": result.returncode,
                },
            )
            return None

    gtxt = gen_path.read_text(encoding="utf-8")
    if "run_cf_main_stdin" in gtxt or "include_gen_run_cf_main.rs" in gtxt:
        problem_dir = gen_path.parent.parent
        cerr = compile_cf_main_bin(problem_dir)
        if cerr:
            print(f"  ❌ {name}: rustc main.rs -> tests/cf_main_bin failed", file=sys.stderr)
            append_pipeline_error(
                name,
                "cf_main_compile_failed",
                cerr[:32000],
                extra={"gen_rs": str(gen_path), "problem_dir": str(problem_dir)},
            )
            return None

    return binary


def _env_for_cf_gen_run(gen_rs: Path) -> dict[str, str] | None:
    """If ``gen.rs`` runs ``main.rs`` via ``include_gen_run_cf_main.rs``, set ``GEN_CF_MAIN_BIN``."""
    if not gen_rs.is_file():
        return None
    g = gen_rs.read_text(encoding="utf-8")
    if "include_gen_run_cf_main.rs" not in g and "run_cf_main_stdin" not in g:
        return None
    exe = gen_rs.parent / "cf_main_bin"
    if not exe.is_file():
        return None
    env = dict(os.environ)
    env["GEN_CF_MAIN_BIN"] = str(exe.resolve())
    return env


def run_generator(
    binary: Path,
    timeout: int = DEFAULT_RUN_TIMEOUT,
    run_argv: list[str] | None = None,
) -> str:
    """Run a compiled generator binary.

    Optional *run_argv* is appended after the binary path (e.g. ``seed``, ``goal``).

    Returns ``"passed"``, ``"failed"``, or ``"timeout"``.
    """
    name = problem_name(binary.parent / "gen.rs")
    argv = [str(binary)] + (run_argv or [])
    gen_rs = binary.parent / "gen.rs"
    run_env = _env_for_cf_gen_run(gen_rs)
    try:
        result = subprocess.run(
            argv,
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=timeout,
            env=run_env,
        )
    except subprocess.TimeoutExpired:
        print(f"  ⏰ {name}: execution timed out ({timeout}s)")
        append_pipeline_error(
            name,
            "generator_run_timeout",
            f"Generator binary timed out after {timeout}s",
            extra={"gen_rs": str(binary.parent / "gen.rs"), "argv": argv},
        )
        return "timeout"
    if result.returncode != 0:
        err = (result.stderr or result.stdout or "").strip()
        print(f"  ❌ {name}: runtime error\n{result.stderr.strip()}")
        append_pipeline_error(
            name,
            "generator_runtime_failed",
            err or f"exit code {result.returncode}",
            extra={
                "gen_rs": str(binary.parent / "gen.rs"),
                "returncode": result.returncode,
                "argv": argv,
            },
        )
        return "failed"

    jsonl_path = binary.parent / "testcases.jsonl"
    if not jsonl_path.exists():
        print(f"  ❌ {name}: testcases.jsonl not created")
        append_pipeline_error(
            name,
            "testcases_jsonl_missing",
            "Generator exited 0 but tests/testcases.jsonl was not created",
            extra={"gen_rs": str(binary.parent / "gen.rs"), "argv": argv},
        )
        return "failed"

    line_count = sum(1 for _ in open(jsonl_path))
    print(f"  ✅ {name}: {line_count} test cases -> {jsonl_path.relative_to(REPO_ROOT)}")
    _verify_cf_stdio_jsonl(name)
    return "passed"


def _process_one(
    gen_path: Path,
    compile_timeout: int = DEFAULT_COMPILE_TIMEOUT,
    run_timeout: int = DEFAULT_RUN_TIMEOUT,
    run_argv: list[str] | None = None,
) -> tuple[str, str, str]:
    """Compile and run a single generator.

    Returns ``(name, status, message)`` where *status* is one of
    ``"passed"``, ``"failed"``, or ``"timeout"``.

    Designed to be called from a process pool — all output is captured
    and returned as a string instead of printed directly.
    """
    name = problem_name(gen_path)
    lines: list[str] = []

    # Use a temp file for the binary to avoid collisions in parallel runs
    tmp_fd, tmp_path = tempfile.mkstemp(prefix=f"gen_{name}_", suffix="")
    os.close(tmp_fd)
    binary = Path(tmp_path)

    try:
        serde_json = find_rlib("libserde_json-*.rlib")
        serde = find_rlib("libserde-*.rlib")
        if not serde_json or not serde:
            detail = f"serde rlibs not found in {DEPS_DIR}"
            append_pipeline_error(
                name,
                "serde_rlibs_missing",
                detail,
                extra={"gen_rs": str(gen_path), "deps_dir": str(DEPS_DIR)},
            )
            return name, "failed", f"  ❌ {name}: {detail}"

        vb = verus_binary()
        cmd = [
            vb, "--compile",
            "--rlimit", "300000",
            str(gen_path),
            "-L", f"dependency={DEPS_DIR}",
            "--extern", f"serde_json={serde_json}",
            "--extern", f"serde={serde}",
            "-o", str(binary),
        ]

        try:
            comp = subprocess.run(cmd, cwd=REPO_ROOT, capture_output=True, text=True,
                                  timeout=compile_timeout)
        except subprocess.TimeoutExpired:
            append_pipeline_error(
                name,
                "verus_compile_timeout",
                f"Verus --compile timed out after {compile_timeout}s",
                extra={"gen_rs": str(gen_path)},
            )
            return name, "timeout", f"  ⏰ {name}: compilation timed out ({compile_timeout}s)"
        output = comp.stdout + comp.stderr
        if comp.returncode != 0 and "0 errors" not in output:
            lines.append(f"  ❌ {name}: compilation/verification failed")
            for line in output.splitlines():
                if "error" in line.lower() or "verification" in line.lower():
                    lines.append(f"     {line}")
            append_pipeline_error(
                name,
                "verus_compile_failed",
                output.strip() or "compilation failed with empty output",
                extra={"gen_rs": str(gen_path), "returncode": comp.returncode},
            )
            return name, "failed", "\n".join(lines)

        # Run
        argv = [str(binary)] + (run_argv or [])
        run_env = _env_for_cf_gen_run(gen_path)
        try:
            run = subprocess.run(
                argv,
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                timeout=run_timeout,
                env=run_env,
            )
        except subprocess.TimeoutExpired:
            append_pipeline_error(
                name,
                "generator_run_timeout",
                f"Generator binary timed out after {run_timeout}s",
                extra={"gen_rs": str(gen_path), "argv": argv},
            )
            return name, "timeout", f"  ⏰ {name}: execution timed out ({run_timeout}s)"
        if run.returncode != 0:
            err = (run.stderr or run.stdout or "").strip()
            append_pipeline_error(
                name,
                "generator_runtime_failed",
                err or f"exit code {run.returncode}",
                extra={
                    "gen_rs": str(gen_path),
                    "returncode": run.returncode,
                    "argv": argv,
                },
            )
            return name, "failed", f"  ❌ {name}: runtime error\n{run.stderr.strip()}"

        jsonl_path = gen_path.parent / "testcases.jsonl"
        if not jsonl_path.exists():
            append_pipeline_error(
                name,
                "testcases_jsonl_missing",
                "Generator exited 0 but tests/testcases.jsonl was not created",
                extra={"gen_rs": str(gen_path), "argv": argv},
            )
            return name, "failed", f"  ❌ {name}: testcases.jsonl not created"

        line_count = sum(1 for _ in open(jsonl_path))
        _verify_cf_stdio_jsonl(name)
        return name, "passed", f"  ✅ {name}: {line_count} test cases -> {jsonl_path.relative_to(REPO_ROOT)}"
    finally:
        binary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("problems", nargs="*",
                        help="Problem names to run (e.g., lc1 lc231). Omit for all.")
    parser.add_argument("--list", action="store_true",
                        help="List available generators and exit.")
    parser.add_argument("-j", "--jobs", type=int, default=1, metavar="N",
                        help="Number of parallel workers (default: 1).")
    parser.add_argument(
        "--timeout",
        type=int,
        default=None,
        metavar="SECS",
        help=(
            "If set, use this timeout (seconds) for **both** Verus compile and generator run. "
            "Otherwise use --compile-timeout and --run-timeout."
        ),
    )
    parser.add_argument(
        "--compile-timeout",
        type=int,
        default=DEFAULT_COMPILE_TIMEOUT,
        metavar="SECS",
        help=f"Timeout for Verus --compile of gen.rs (default: {DEFAULT_COMPILE_TIMEOUT}).",
    )
    parser.add_argument(
        "--run-timeout",
        type=int,
        default=DEFAULT_RUN_TIMEOUT,
        metavar="SECS",
        help=(
            f"Timeout for running the generator binary (default: {DEFAULT_RUN_TIMEOUT}); "
            "this step executes code.rs for outputs."
        ),
    )
    parser.add_argument(
        "--seed",
        default=None,
        help="Optional first CLI argument to each generator (many gen.rs use argv[1] as RNG seed).",
    )
    parser.add_argument(
        "--goal",
        default=None,
        help="Optional second CLI argument (e.g. target number of cases for generators that read argv[2]).",
    )
    args = parser.parse_args()

    compile_timeout = args.timeout if args.timeout is not None else args.compile_timeout
    run_timeout = args.timeout if args.timeout is not None else args.run_timeout

    run_argv: list[str] = []
    if args.seed is not None:
        run_argv.append(str(args.seed))
    if args.goal is not None:
        run_argv.append(str(args.goal))

    all_gens = find_all_generators()

    if args.list:
        print(f"Available generators ({len(all_gens)}):")
        for g in all_gens:
            print(f"  {problem_name(g):12s} {g.relative_to(REPO_ROOT)}")
        return 0

    if args.problems:
        selected = []
        for name in args.problems:
            matches = [g for g in all_gens if problem_name(g) == name]
            if not matches:
                print(f"  ⚠️  No generator found for '{name}'", file=sys.stderr)
            else:
                selected.extend(matches)
        if not selected:
            print("No matching generators found.", file=sys.stderr)
            return 1
    else:
        selected = all_gens

    if not selected:
        print("No generators found.")
        return 0

    print(
        f"Running {len(selected)} generator(s) with {args.jobs} worker(s) "
        f"(compile_timeout={compile_timeout}s, run_timeout={run_timeout}s)...\n"
    )

    if not build_deps():
        return 1

    passed = 0
    failed_names: list[str] = []
    timeout_names: list[str] = []

    if args.jobs == 1:
        # Sequential mode — keeps existing behaviour with live output
        for gen_path in selected:
            name = problem_name(gen_path)
            print(f"\n[{name}] Compiling...")
            comp_result = compile_generator(gen_path, timeout=compile_timeout)
            if comp_result == "timeout":
                timeout_names.append(name)
                continue
            if not isinstance(comp_result, Path):
                failed_names.append(name)
                continue

            print(f"[{name}] Running...")
            status = run_generator(comp_result, timeout=run_timeout, run_argv=run_argv)
            if status == "passed":
                passed += 1
            elif status == "timeout":
                timeout_names.append(name)
            else:
                failed_names.append(name)
    else:
        # Parallel mode
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            futures = {
                pool.submit(_process_one, g, compile_timeout, run_timeout, run_argv): g
                for g in selected
            }
            for future in as_completed(futures):
                name, status, message = future.result()
                print(message)
                if status == "passed":
                    passed += 1
                elif status == "timeout":
                    timeout_names.append(name)
                else:
                    failed_names.append(name)

    total = passed + len(failed_names) + len(timeout_names)
    print(f"\n{'=' * 40}")
    print(f"Results: {passed} passed, {len(failed_names)} failed, {len(timeout_names)} timed out, {total} total")
    if failed_names:
        print(f"\nFailed ({len(failed_names)}):")
        for name in sorted(failed_names):
            print(f"  ❌ {name}")
    if timeout_names:
        print(f"\nTimed out ({len(timeout_names)}):")
        for name in sorted(timeout_names):
            print(f"  ⏰ {name}")
    return 1 if failed_names or timeout_names else 0


if __name__ == "__main__":
    sys.exit(main())
