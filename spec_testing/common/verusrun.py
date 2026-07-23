"""The single Verus entry point.

run_verus() invokes the bundled Verus, parses --output-json, and classifies
the result into a typed status. When Verus cannot run (missing binary /
broken toolchain) it returns status "tool_error" so callers degrade to typed
verdicts instead of crashing.
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path

from .config import REPO_ROOT, get

RLIMIT_MSG = "Resource limit (rlimit) exceeded"


@dataclass
class VerusResult:
    status: str        # verified|verify_failed|compile_error|vir_error|timeout|rlimit|tool_error
    func_details: dict[str, bool] = field(default_factory=dict)


@lru_cache(maxsize=1)
def find_verus_binary() -> str | None:
    cfg = get("paths", "verus_bin", "auto")
    if cfg and cfg != "auto":
        return cfg if Path(cfg).exists() else None
    for cand in (REPO_ROOT / "verus" / "verus.exe", REPO_ROOT / "verus" / "verus"):
        if cand.exists():
            return str(cand)
    env = os.environ.get("VERUS")
    if env and Path(env).exists():
        return env
    return shutil.which("verus")


def _classify(exit_code: int, stdout: str, stderr: str, timed_out: bool) -> tuple[str, dict | None]:
    if timed_out:
        return "timeout", None

    raw: dict | None = None
    try:
        raw = json.loads(stdout) if stdout.strip() else None
    except json.JSONDecodeError:
        raw = None

    compile_err = False
    rlimit_hit = False
    for line in stderr.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            d = json.loads(line)
        except json.JSONDecodeError:
            continue
        if d.get("$message_type") != "diagnostic":
            continue
        code = ""
        cobj = d.get("code")
        if isinstance(cobj, dict) and cobj.get("code"):
            code = cobj["code"]
        if code.startswith("E0"):
            compile_err = True
        if RLIMIT_MSG in d.get("message", ""):
            rlimit_hit = True

    if raw is not None and raw.get("verification-results", {}).get("encountered-vir-error"):
        return "vir_error", raw
    if compile_err:
        return "compile_error", raw
    if rlimit_hit:
        return "rlimit", raw
    if raw is not None:
        errors = raw.get("verification-results", {}).get("errors", 0)
        return ("verified" if exit_code == 0 and errors == 0 else "verify_failed"), raw
    return "tool_error", None


def _parse_func_details(raw: dict | None) -> dict[str, bool]:
    """Parse per-function verdicts from --output-json func-details."""
    out: dict[str, bool] = {}
    if not raw:
        return out
        
    # 1. Initialize from func-details keys (defaulting to True)
    fd = raw.get("func-details")
    if isinstance(fd, dict):
        for name, info in fd.items():
            ok = True
            if isinstance(info, bool):
                ok = info
            elif isinstance(info, dict):
                if "success" in info:
                    ok = bool(info["success"])
                elif "verified" in info:
                    ok = bool(info["verified"])
                elif "errors" in info:
                    ok = (info.get("errors", 1) == 0)
            out[str(name)] = ok

    # 2. Update from smt-run-module-times function-breakdown (if present)
    times_ms = raw.get("times-ms", {})
    smt = times_ms.get("smt", {})
    smt_run_module = smt.get("smt-run-module-times", [])
    if isinstance(smt_run_module, list):
        for module_data in smt_run_module:
            if isinstance(module_data, dict):
                breakdown = module_data.get("function-breakdown", [])
                if isinstance(breakdown, list):
                    for fn_data in breakdown:
                        if isinstance(fn_data, dict):
                            fn_name = fn_data.get("function")
                            if fn_name:
                                out[str(fn_name)] = bool(fn_data.get("success", False))

    # 3. Add short names mapping
    for name_str, ok in list(out.items()):
        if "::" in name_str:
            short_name = name_str.split("::")[-1]
            out[short_name] = ok

    return out


def run_verus(
    file: Path,
    *,
    rlimit: float = 10,
    verify_function: str | None = None,
    verify_root: bool = False,
    no_cheating: bool = False,
    timeout_s: int = 300,
) -> VerusResult:
    binary = find_verus_binary()
    if binary is None:
        return VerusResult(status="tool_error")

    cmd = [
        binary, str(file),
        "--crate-type=lib",
        "--rlimit", str(rlimit),
        "--multiple-errors", "20",
        "--expand-errors",
        "--output-json",
        "--time",
        "--error-format=json",
        "--smt-option", "smt.random_seed=7",
    ]
    z3_memory_mb = int(get("run", "z3_memory_mb", 0))
    if z3_memory_mb > 0:
        # hard Z3 memory cap: a runaway matching loop becomes UNDECIDED
        # instead of exhausting the machine
        cmd += ["--smt-option", f"memory_max_size={z3_memory_mb}"]
    if no_cheating:
        cmd.append("--no-cheating")
    if verify_function is not None:
        if verify_root:
            cmd.append("--verify-root")
        # Ensure exact matching of function name by using *fn wildcard to match ends only,
        # preventing substring collision with spec functions like fn_spec.
        val = verify_function
        if not val.startswith("*"):
            val = f"*{val}"
        cmd += ["--verify-function", val]

    timed_out = False
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout_s,
            encoding="utf-8", errors="replace",
            cwd=str(file.parent),   # rustc artifacts (lib*.rlib) land here, not in CWD
        )
        exit_code = proc.returncode
        stdout, stderr = proc.stdout, proc.stderr
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        exit_code = -1
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", "replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", "replace")
    except (OSError, ValueError):
        return VerusResult(status="tool_error")

    status, raw = _classify(exit_code, stdout, stderr, timed_out)
    return VerusResult(status=status, func_details=_parse_func_details(raw))
