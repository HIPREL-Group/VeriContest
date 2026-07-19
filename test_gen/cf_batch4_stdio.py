#!/usr/bin/env python3
"""Verify ``main.rs`` against ``tests/testcases.jsonl`` for Codeforces encoder problems.

Each JSONL line is ``{"input": "<stdin text>", "output": "<stdout text>"}`` (both
strings).  For legacy structured ``input`` objects, ``build_stdin`` reconstructs
stdin (``t=1`` style except cf1989A).

Run from repo root::

    python3 test_gen/cf_batch4_stdio.py --batch test_gen/_cf_main_stdin_batch_4.txt --write
    python3 test_gen/cf_batch4_stdio.py --problem cf1840C   # verify only

``--write`` rewrites lines to the string-only ``input`` / ``output`` form.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# Problems with a ``build_stdin`` implementation in this module.
ENCODER_PIDS = frozenset(
    {
        "cf1840C",
        "cf1845B",
        "cf1855A",
        "cf1857D",
        "cf1858A",
        "cf1862D",
        "cf1873B",
        "cf1881C",
        "cf1883C",
        "cf1901A",
        "cf1901B",
        "cf1902B",
        "cf1915C",
        "cf1921A",
        "cf1921C",
        "cf1927D",
        "cf1931C",
        "cf1985B",
        "cf1985D",
        "cf1989A",
        "cf1993C",
    }
)


def _join_ints(xs: list) -> str:
    return " ".join(str(int(x)) for x in xs)


def _row01_to_hashdot(row: list) -> str:
    return "".join("#" if int(v) == 1 else "." for v in row)


def _row_nums_to_letters(row: list) -> str:
    return "".join(chr(ord("a") + int(v)) for v in row)


def build_stdin(pid: str, inp: dict) -> str:
    if pid == "cf1840C":
        n, k, q = int(inp["n"]), int(inp["k"]), int(inp["q"])
        a = inp["a"]
        return f"1\n{n} {k} {q}\n{_join_ints(a)}\n"
    if pid == "cf1845B":
        return (
            "1\n"
            f"{int(inp['ax'])} {int(inp['ay'])} {int(inp['bx'])} {int(inp['by'])} "
            f"{int(inp['cx'])} {int(inp['cy'])}\n"
        )
    if pid == "cf1855A":
        p = inp["p"]
        n = len(p)
        return f"1\n{n}\n{_join_ints(p)}\n"
    if pid == "cf1857D":
        a, b = inp["a"], inp["b"]
        n = len(a)
        return f"1\n{n}\n{_join_ints(a)}\n{_join_ints(b)}\n"
    if pid == "cf1858A":
        return f"1\n{int(inp['a'])} {int(inp['b'])} {int(inp['c'])}\n"
    if pid == "cf1862D":
        return f"1\n{int(inp['n'])}\n"
    if pid == "cf1873B":
        a = inp["a"]
        n = len(a)
        return f"1\n{n}\n{_join_ints(a)}\n"
    if pid == "cf1881C":
        n = int(inp["n"])
        g = inp["grid"]
        lines = "\n".join(_row_nums_to_letters(row) for row in g)
        return f"1\n{n}\n{lines}\n"
    if pid == "cf1883C":
        n, k = int(inp["n"]), int(inp["k"])
        a = inp["a"]
        return f"1\n{n} {k}\n{_join_ints(a)}\n"
    if pid == "cf1901A":
        arr = inp["a"]
        n = len(arr)
        x = int(inp["x"])
        return f"1\n{n} {x}\n{_join_ints(arr)}\n"
    if pid == "cf1901B":
        c = inp["c"]
        n = len(c)
        return f"1\n{n}\n{_join_ints(c)}\n"
    if pid == "cf1902B":
        n, p, l, t = int(inp["n"]), int(inp["p"]), int(inp["l"]), int(inp["t"])
        return f"1\n{n} {p} {l} {t}\n"
    if pid == "cf1915C":
        a = inp["a"]
        n = len(a)
        return f"1\n{n}\n{_join_ints(a)}\n"
    if pid == "cf1921A":
        xs, ys = inp["xs"], inp["ys"]
        parts = ["1"]
        for i in range(4):
            parts.append(f"{int(xs[i])} {int(ys[i])}")
        return "\n".join(parts) + "\n"
    if pid == "cf1921C":
        m = inp["m"]
        n = len(m)
        f, a, b = int(inp["f"]), int(inp["a"]), int(inp["b"])
        return f"1\n{n} {f} {a} {b}\n{_join_ints(m)}\n"
    if pid == "cf1927D":
        a = inp["a"]
        queries = inp["queries"]
        n = len(a)
        q = len(queries)
        flat: list[str] = ["1", str(n), *_join_ints(a).split(), str(q)]
        for lr in queries:
            flat.extend(str(int(x)) for x in lr)
        return " ".join(flat) + "\n"
    if pid == "cf1931C":
        a = inp["a"]
        n = len(a)
        return f"1\n{n}\n{_join_ints(a)}\n"
    if pid == "cf1985B":
        return f"1\n{int(inp['n'])}\n"
    if pid == "cf1985D":
        g = inp["grid"]
        n, m = len(g), len(g[0])
        rows = "\n".join(_row01_to_hashdot(r) for r in g)
        return f"1\n{n} {m}\n{rows}\n"
    if pid == "cf1989A":
        # One coin per testcase line in jsonl (n = 1 in CF stdin).
        return f"1\n{int(inp['x'])} {int(inp['y'])}\n"
    if pid == "cf1993C":
        a = inp["a"]
        n = len(a)
        k = int(inp["period"])
        return f"1\n{n} {k}\n{_join_ints(a)}\n"
    raise KeyError(f"unknown pid {pid}")


def compile_main(problem_dir: Path, dest: Path) -> tuple[bool, str]:
    main_rs = problem_dir / "main.rs"
    if not main_rs.is_file():
        return False, f"missing {main_rs}"
    r = subprocess.run(
        ["rustc", "--edition", "2021", "-O", str(main_rs), "-o", str(dest)],
        cwd=str(problem_dir),
        capture_output=True,
        text=True,
        timeout=120,
    )
    if r.returncode != 0:
        return False, (r.stderr or r.stdout or "rustc failed")[:8000]
    return True, ""


def run_main(bin_path: Path, stdin: str, timeout: float = 30.0) -> tuple[int, str, str]:
    r = subprocess.run(
        [str(bin_path)],
        input=stdin,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return r.returncode, r.stdout, r.stderr


def process_problem(problem_dir: Path, *, write: bool) -> tuple[str, str, str]:
    """Returns (pid, status, detail). status in ok, rustc_fail, verify_fail, skip."""
    pid = problem_dir.name
    if pid not in ENCODER_PIDS:
        return pid, "skip", "no stdin encoder in cf_batch4_stdio.py"
    jsonl = problem_dir / "tests" / "testcases.jsonl"
    if not jsonl.is_file():
        return pid, "skip", "no testcases.jsonl"

    lines_out: list[str] = []
    with tempfile.TemporaryDirectory() as td:
        bin_path = Path(td) / "cf_main"
        ok, err = compile_main(problem_dir, bin_path)
        if not ok:
            return pid, "rustc_fail", err

        with open(jsonl, encoding="utf-8") as f:
            for lineno, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                obj = json.loads(line)
                inp = obj.get("input")
                if isinstance(inp, str):
                    stdin = inp
                elif isinstance(inp, dict):
                    try:
                        stdin = build_stdin(pid, inp)
                    except Exception as e:
                        return pid, "verify_fail", f"line {lineno}: build_stdin: {e}"
                else:
                    return pid, "verify_fail", f"line {lineno}: bad input type {type(inp)!r}"
                rc, out, err = run_main(bin_path, stdin)
                if rc != 0:
                    return pid, "verify_fail", f"line {lineno}: rc={rc} stderr={err[:500]!r}"
                want = obj.get("output")
                if want is not None:
                    want_s = want if isinstance(want, str) else str(want)
                    if want_s != out:
                        return (
                            pid,
                            "verify_fail",
                            f"line {lineno}: output mismatch\n--- want ---\n{want_s!r}\n--- got ---\n{out!r}",
                        )
                lines_out.append(
                    json.dumps({"input": stdin, "output": out}, ensure_ascii=False)
                )

    if write:
        jsonl.write_text("\n".join(lines_out) + "\n", encoding="utf-8")
    return pid, "ok", f"{len(lines_out)} lines"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--batch", type=Path, help="text file of problem ids, one per line")
    ap.add_argument("--problem", action="append", default=[], metavar="PID", help="cfXXXX (repeatable)")
    ap.add_argument("--write", action="store_true", help="rewrite tests/testcases.jsonl")
    args = ap.parse_args()

    pids: list[str] = []
    if args.batch:
        for raw in args.batch.read_text(encoding="utf-8").splitlines():
            s = raw.strip()
            if s and not s.startswith("#"):
                pids.append(s)
    pids.extend(args.problem)
    if not pids:
        print("no problems (use --batch or --problem)", file=sys.stderr)
        return 1

    root = REPO_ROOT / "benchmark" / "codeforces"
    failed = 0
    for pid in pids:
        d = root / pid
        st, status, detail = "", "", ""
        if not d.is_dir():
            print(f"{pid}: MISSING_DIR")
            failed += 1
            continue
        pid, status, detail = process_problem(d, write=args.write)
        if status == "skip":
            tag = "SKIP"
        elif args.write and status == "ok":
            tag = "WROTE"
        elif status == "ok":
            tag = "OK"
        else:
            tag = status.upper()
            failed += 1
        print(f"{pid}: {tag} {detail}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
