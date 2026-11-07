"""
check_consistency_cf.py — Check file consistency of Codeforces benchmark folders.

Usage:
    python scripts/check_consistency_cf.py <folder> [<folder> ...]
    python scripts/check_consistency_cf.py --all

Checks performed for each benchmark folder:
  (1) Required files exist: main.rs, code.rs, code_spec.rs, spec.rs, verified.rs
  (2) code.rs     ⊂ main.rs       (with code_rs normalization)
  (3) code.rs     ⊂ code_spec.rs  (with code_rs normalization)
  (4) code.rs     ⊂ verified.rs   (with code_rs normalization)
  (5) code_spec.rs ⊂ verified.rs  (with base normalization)
  (6) spec.rs     ⊂ code_spec.rs  (with base normalization)
  (7) spec.rs     ⊂ verified.rs   (with base normalization)

Subset means: every non-empty normalized line of the smaller file appears
in the larger file in the same relative order (ordered sub-sequence).

Two normalization levels:
  - normalize_base: applied to ALL comparisons — collapses whitespace,
    drops empty / lone-brace lines, strips trailing '{'.
  - normalize_code_rs: extends normalize_base with Verus → plain-Rust
    transforms (named returns, .set()), applied only when code.rs is the
    smaller side.

Exit code 0 if all folders pass; 1 if any folder fails.
"""

import re
import sys
import os
import glob
import argparse


REQUIRED_FILES = ["main.rs", "code.rs", "code_spec.rs", "spec.rs", "verified.rs"]


# ---------------------------------------------------------------------------
# Normalization  (identical to check_consistency.py)
# ---------------------------------------------------------------------------

def _strip_use_blocks(lines: list[str]) -> list[str]:
    """Remove all ``use`` import statements, including multi-line ones."""
    result: list[str] = []
    in_use = False
    for line in lines:
        stripped = line.strip()
        if in_use:
            if ";" in stripped:
                in_use = False
            continue
        if stripped.startswith("use "):
            if ";" in stripped:
                continue
            else:
                in_use = True
                continue
        result.append(line)
    return result


def normalize_base(line: str) -> str:
    """Normalize a single line for comparison (applied to all file pairs)."""
    s = line.strip()
    if s == "" or s == "{" or s == "}":
        return ""
    if s.endswith("{"):
        s = s[:-1].rstrip()
    s = re.sub(r"\s+", " ", s)
    return s


_NAMED_RETURN_RE = re.compile(r"->\s*\(\s*\w+\s*:\s*(.+)\)")
_SET_RE = re.compile(r"(\w+)\.set\((.+),\s*(.+)\);")


def normalize_code_rs(line: str) -> str:
    """Extended normalization for code.rs comparisons."""
    s = normalize_base(line)
    if s == "":
        return s
    s = _NAMED_RETURN_RE.sub(lambda m: f"-> {m.group(1).rstrip()}", s)
    s = _SET_RE.sub(lambda m: f"{m.group(1)}[{m.group(2).strip()}] = {m.group(3).strip()};", s)
    return s


# ---------------------------------------------------------------------------
# Ordered-subset check
# ---------------------------------------------------------------------------

def read_lines(filepath: str) -> list[str]:
    """Read a file and return its raw lines with use-blocks removed."""
    with open(filepath, "r", encoding="utf-8") as f:
        lines = [line.rstrip() for line in f.readlines()]
    return _strip_use_blocks(lines)


def is_ordered_subset(small_lines: list[str], big_lines: list[str],
                      normalizer=normalize_base):
    """Check whether small_lines is an ordered sub-sequence of big_lines
    after applying *normalizer* to every line.

    Returns (True, []) on success, or (False, list_of_issues) on failure.
    """
    norm_small = [(i + 1, normalizer(l)) for i, l in enumerate(small_lines)]
    norm_big = [normalizer(l) for l in big_lines]

    norm_small = [(lineno, s) for lineno, s in norm_small if s != ""]
    norm_big = [s for s in norm_big if s != ""]

    issues = []
    big_idx = 0
    big_len = len(norm_big)

    for small_lineno, sline in norm_small:
        found = False
        while big_idx < big_len:
            if norm_big[big_idx] == sline:
                big_idx += 1
                found = True
                break
            big_idx += 1

        if not found:
            issues.append(
                f"  line {small_lineno}: {sline!r} not found (in order) in target"
            )

    return (len(issues) == 0, issues)


# ---------------------------------------------------------------------------
# Folder check
# ---------------------------------------------------------------------------

def check_folder(folder: str):
    """Run all consistency checks on a single Codeforces benchmark folder.

    Returns (pass: bool, messages: list[str]).
    """
    name = os.path.basename(folder)
    messages = []
    passed = True

    # ------------------------------------------------------------------
    # Check 1: Required files exist
    # ------------------------------------------------------------------
    missing = [f for f in REQUIRED_FILES
               if not os.path.isfile(os.path.join(folder, f))]
    if missing:
        messages.append(f"[FAIL] {name}: missing files: {', '.join(missing)}")
        return False, messages

    main = read_lines(os.path.join(folder, "main.rs"))
    code = read_lines(os.path.join(folder, "code.rs"))
    code_spec = read_lines(os.path.join(folder, "code_spec.rs"))
    spec = read_lines(os.path.join(folder, "spec.rs"))
    verified = read_lines(os.path.join(folder, "verified.rs"))

    # ------------------------------------------------------------------
    # Check 2: code.rs ⊂ main.rs
    #           (algorithm in code.rs must appear in main.rs)
    # ------------------------------------------------------------------
    ok, issues = is_ordered_subset(code, main, normalizer=normalize_base)
    if not ok:
        passed = False
        messages.append(
            f"[FAIL] {name}: code.rs is NOT an ordered subset of main.rs")
        messages.extend(issues)

    # ------------------------------------------------------------------
    # Check 3-4: code.rs ⊂ code_spec.rs  AND  code.rs ⊂ verified.rs
    # ------------------------------------------------------------------
    for target_name, target_lines in [("code_spec.rs", code_spec),
                                       ("verified.rs", verified)]:
        ok, issues = is_ordered_subset(code, target_lines,
                                       normalizer=normalize_code_rs)
        if not ok:
            passed = False
            messages.append(
                f"[FAIL] {name}: code.rs is NOT an ordered subset of {target_name}")
            messages.extend(issues)

    # ------------------------------------------------------------------
    # Check 5: code_spec.rs ⊂ verified.rs
    # ------------------------------------------------------------------
    ok, issues = is_ordered_subset(code_spec, verified,
                                   normalizer=normalize_base)
    if not ok:
        passed = False
        messages.append(
            f"[FAIL] {name}: code_spec.rs is NOT an ordered subset of verified.rs")
        messages.extend(issues)

    # ------------------------------------------------------------------
    # Check 6-7: spec.rs ⊂ code_spec.rs  AND  spec.rs ⊂ verified.rs
    # ------------------------------------------------------------------
    for target_name, target_lines in [("code_spec.rs", code_spec),
                                       ("verified.rs", verified)]:
        ok, issues = is_ordered_subset(spec, target_lines,
                                       normalizer=normalize_base)
        if not ok:
            passed = False
            messages.append(
                f"[FAIL] {name}: spec.rs is NOT an ordered subset of {target_name}")
            messages.extend(issues)

    if passed:
        messages.append(f"[PASS] {name}")

    return passed, messages


# ---------------------------------------------------------------------------
# Discovery & CLI
# ---------------------------------------------------------------------------

def _load_ignore_list(cf_dir: str) -> set[str]:
    """Read .benchmark-ignore and return the set of directory names to skip."""
    ignore_path = os.path.join(cf_dir, ".benchmark-ignore")
    ignored: set[str] = set()
    if not os.path.isfile(ignore_path):
        return ignored
    with open(ignore_path, encoding="utf-8") as f:
        for line in f:
            entry = line.strip()
            if entry and not entry.startswith("#"):
                ignored.add(entry)
    return ignored


def discover_all_benchmarks() -> list[str]:
    """Find all cf* benchmark directories under problems/codeforces/,
    excluding any listed in .benchmark-ignore."""
    # This script lives in benchmarks/verus/skills/add-codeforces-benchmark/scripts/, so benchmarks/verus/
    # is three levels up.
    verus_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
    cf_dir = os.path.join(verus_root, "problems", "codeforces")
    ignored = _load_ignore_list(cf_dir)
    dirs = sorted(glob.glob(os.path.join(cf_dir, "cf*")))
    return [d for d in dirs if os.path.isdir(d) and os.path.basename(d) not in ignored]


def main():
    parser = argparse.ArgumentParser(
        description="Check Codeforces benchmark folder consistency."
    )
    parser.add_argument(
        "folders",
        nargs="*",
        help="Benchmark folder(s) to check.",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Check all benchmarks under problems/codeforces/.",
    )
    args = parser.parse_args()

    if args.all:
        folders = discover_all_benchmarks()
        if not folders:
            print("No benchmark folders found.")
            sys.exit(1)
    elif args.folders:
        folders = args.folders
    else:
        parser.print_help()
        sys.exit(1)

    total = 0
    failed = 0

    for folder in folders:
        folder = os.path.abspath(folder)
        if not os.path.isdir(folder):
            print(f"[SKIP] {folder}: not a directory")
            continue
        total += 1
        ok, msgs = check_folder(folder)
        for msg in msgs:
            print(msg)
        if not ok:
            failed += 1

    print()
    print(f"Total: {total}  Passed: {total - failed}  Failed: {failed}")

    sys.exit(1 if failed > 0 else 0)


if __name__ == "__main__":
    main()
