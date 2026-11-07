"""Build an executable test harness around a candidate program.

LeetCode problems use ``tests/reference_oracle.rs``: a JSON-lines driver with an
``include!("../code.rs");`` slot that receives the candidate. Codeforces
problems use ``main.rs``: the candidate replaces its ``impl Solution`` block and
the original stdin/stdout ``main`` is kept.

Argument parsing, input-key compatibility, and output serialization belong to
the benchmark's drivers, which the evaluator uses as they are.
"""
from __future__ import annotations

import re
from pathlib import Path

INCLUDE = 'include!("../code.rs");'
_IMPL_SOL = re.compile(r"\bimpl\s+Solution\s*\{")
_MAIN_FN = re.compile(r"\bfn\s+main\s*\([^)]*\)\s*")
_VERUS_HINT = re.compile(
    r"\b(verus!|vstd::|requires|ensures|invariant|decreases|recommends|proof|spec|ghost|tracked)\b")


class HarnessError(ValueError):
    pass


def _block_end(source: str, open_brace: int) -> int | None:
    """Index of the ``}`` matching the ``{`` at ``open_brace`` (ignores strings)."""
    depth = 0
    for i in range(open_brace, len(source)):
        if source[i] == "{":
            depth += 1
        elif source[i] == "}":
            depth -= 1
            if depth == 0:
                return i
    return None


def _strip_blocks(code: str, head: re.Pattern) -> str:
    """Remove every match of ``head`` together with its following ``{...}``."""
    while True:
        m = head.search(code)
        if not m:
            return code
        open_brace = code.find("{", m.end() - 1)
        end = _block_end(code, open_brace) if open_brace != -1 else None
        if end is None:
            return code
        code = code[: m.start()] + code[end + 1:]


def _impl_solution_span(source: str) -> tuple[int, int] | None:
    m = _IMPL_SOL.search(source)
    if not m:
        return None
    end = _block_end(source, source.find("{", m.start()))
    return None if end is None else (m.start(), end + 1)


def is_verus(code: str) -> bool:
    return bool(_VERUS_HINT.search(code) or re.search(r"->\s*\(\s*\w+\s*:", code))


# -----------------------------------------------------------------------------
# Templates
# -----------------------------------------------------------------------------
def template(problem_dir: Path) -> tuple[str, str]:
    """Return ``(mode, text)``; mode is ``oracle`` (JSON lines) or ``main`` (stdio)."""
    oracle = problem_dir / "tests" / "reference_oracle.rs"
    reference = problem_dir / "code.rs"
    reference_code = reference.read_text() if reference.is_file() else ""
    if oracle.is_file():
        return "oracle", oracle.read_text()
    inlined = problem_dir / "tests" / "harness.rs"
    if inlined.is_file() and reference_code and reference_code in inlined.read_text():
        return "oracle", inlined.read_text().replace(reference_code, INCLUDE, 1)
    main = problem_dir / "main.rs"
    if main.is_file():
        return "main", main.read_text()
    raise HarnessError(f"no test harness for {problem_dir}")


# -----------------------------------------------------------------------------
# Splicing the candidate into the driver.
# -----------------------------------------------------------------------------
def _strip_verus_wrapper(code: str) -> str:
    """If code is wrapped in ``verus! { ... }``, unwrap one level."""
    m = re.search(r"verus!\s*\{", code)
    if not m:
        return code
    open_pos = code.find("{", m.start())
    end = _block_end(code, open_pos) if open_pos != -1 else None
    if end is None:
        return code
    return code[: m.start()] + code[open_pos + 1: end] + code[end + 1:]


def clean_code_for_harness(code: str) -> str:
    """Remove pieces that clash with the harness: its own main, std::io and vstd
    imports, and the ``struct Solution`` declaration."""
    code = _strip_verus_wrapper(code)
    code = _strip_blocks(code, _MAIN_FN)
    code = re.sub(r"^[ \t]*use\s+vstd::[^;]*;\s*$", "", code, flags=re.M)
    code = re.sub(r"^[ \t]*use\s+std::io(?:::[^;]*)?;\s*$", "", code, flags=re.M)
    return re.sub(r"^[ \t]*(?:pub\s+)?struct\s+Solution\s*;\s*$", "", code, flags=re.M)


_FN_NAME = re.compile(r"\bfn\s+([A-Za-z_]\w*)")


def _drop_redefined_fns(source: str, code: str) -> str:
    """Drop driver fns (free, or in an ``impl Solution``) that ``code`` defines
    too, e.g. helpers main.rs repeats from code.rs; ``main`` stays. An
    ``impl Solution`` left empty is removed."""
    for name in set(_FN_NAME.findall(code)) - {"main"}:
        source = _strip_blocks(source, re.compile(rf"^[ \t]*(?:pub\s+)?fn\s+{re.escape(name)}\b[^{{;]*\{{", re.M))
    return re.sub(r"\bimpl\s+Solution\s*\{\s*\}\s*", "", source)


def _replace_impl_solution(main_src: str, new_impl: str) -> str:
    span = _impl_solution_span(main_src)
    if span is None:
        raise HarnessError("impl Solution { ... } not found in main.rs")
    return (_drop_redefined_fns(main_src[: span[0]], new_impl) + new_impl
            + _drop_redefined_fns(main_src[span[1]:], new_impl))


def build_main_rs_source(main_text: str, cleaned: str) -> str:
    """Replace main.rs's ``impl Solution`` with the candidate's (or wrap bare methods)."""
    span = _impl_solution_span(cleaned)
    impl = cleaned[span[0]: span[1]] if span else f"impl Solution {{\n{cleaned.strip()}\n}}"
    return _replace_impl_solution(main_text, impl)


_PROOF_BLOCK = re.compile(r"\bproof\s*\{")
_WHILE_LOOP_SPEC = re.compile(
    r"(\bwhile\b[^\n]+)\s*\n\s*invariant\b[\s\S]*?(?:\n\s*decreases\b[^\n]+)?\s*\n\s*\{", re.M)


def _strip_pub_fn_requires_ensures(code: str) -> str:
    lines, out, i = code.split("\n"), [], 0
    while i < len(lines):
        ln = lines[i]
        if re.match(r"^(\s{4})pub fn \w", ln) and "spec fn" not in ln:
            out.append(re.sub(r"->\s*\(\s*\w+\s*:\s*([^)]+)\)", r"-> \1", ln))
            i += 1
            while i < len(lines):
                if re.match(r"^\s{4}\{\s*$", lines[i]):
                    out.append(lines[i])
                    i += 1
                    break
                i += 1
            continue
        out.append(ln)
        i += 1
    return "\n".join(out)


def strip_verus_for_rustc_harness(code: str) -> str:
    """Turn Verus-style ``impl Solution`` into plain Rust for the rustc backend."""
    code = clean_code_for_harness(code)
    code = _strip_blocks(code, re.compile(r"\bpub\s+open\s+spec\s+fn\b"))
    code = _strip_blocks(code, re.compile(r"\bproof\s+fn\b"))
    code = _strip_blocks(code, re.compile(r"\bspec\s+fn\b"))
    code = _strip_blocks(code, _PROOF_BLOCK)
    code = _strip_pub_fn_requires_ensures(code)
    prev = None
    while prev != code:
        prev = code
        code = _WHILE_LOOP_SPEC.sub(lambda m: m.group(1).rstrip() + " {", code)
    code = "\n".join(ln for ln in code.splitlines() if not re.match(r"^\s*let\s+(ghost|tracked)\b", ln))
    code = re.sub(r"^[ \t]*#\[verifier[^\]]*\]\s*$\n?", "", code, flags=re.M)
    code = re.sub(r"^[ \t]*#\[trigger\][^\n]*\n", "", code, flags=re.M)
    code = re.sub(r"\n{3,}", "\n\n", code)
    return code.strip() + "\n"


def _defines_solution(code: str) -> bool:
    return re.search(r"\b(?:pub\s+)?struct\s+Solution\s*;", code) is not None


def _drop_solution_decl(source: str) -> str:
    return re.sub(r"^[ \t]*(?:pub\s+)?struct\s+Solution\s*;\s*$\n?", "", source, count=1, flags=re.M)


def _drop_conflicting_consts(source: str, code: str) -> str:
    for name in set(re.findall(r"^[ \t]*(?:pub\s+)?const\s+([A-Za-z_]\w*)\s*:", code, flags=re.M)):
        source = re.sub(rf"^[ \t]*(?:pub\s+)?const\s+{re.escape(name)}\s*:[^=;]+=[^;]*;\s*$\n?",
                        "", source, flags=re.M)
    return source


def _prepare_verus_code(raw: str) -> str:
    code = _strip_blocks(raw, _MAIN_FN)
    if "verus!" in code:
        return code
    prefix = "" if "vstd::" in code else "use vstd::prelude::*;\n\n"
    return f"{prefix}verus! {{\n\n{code.strip()}\n\n}}\n"


def build_verus_harness_source(mode: str, text: str, raw: str) -> str:
    """Keep Verus code intact and splice it into the runnable harness."""
    code = re.sub(r"^[ \t]*use\s+std::io(?:::[^;]*)?;\s*$\n?", "", _prepare_verus_code(raw), flags=re.M).strip() + "\n"
    if mode == "oracle":
        if _defines_solution(code):
            text = _drop_solution_decl(text)
        return text.replace(INCLUDE, code)
    span = _impl_solution_span(text)
    if span is None:
        raise HarnessError("impl Solution { ... } not found in main.rs")
    text = _drop_conflicting_consts(text[: span[0]] + text[span[1]:], code)
    text = _drop_redefined_fns(text, code)
    if _defines_solution(code):
        text = _drop_solution_decl(text)
    return code + "\n" + text


def build_source(problem_dir: Path, program: str, policy: str) -> tuple[str, str]:
    """Return ``(backend, source)``.

    ``policy`` is ``rustc`` (CodeGen from natural language: plain Rust) or
    ``auto`` (Verus-looking programs are compiled with Verus, others are
    stripped and compiled with rustc).
    """
    mode, text = template(problem_dir)
    if INCLUDE not in text and mode == "oracle":
        raise HarnessError("harness has no include slot")
    if policy == "auto" and is_verus(program):
        return "verus", build_verus_harness_source(mode, text, program)
    code = clean_code_for_harness(program) if policy == "rustc" else \
        clean_code_for_harness(strip_verus_for_rustc_harness(program))
    if mode == "oracle":
        return "rustc", text.replace(INCLUDE, code)
    return "rustc", build_main_rs_source(text, code)
