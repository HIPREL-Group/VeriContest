"""Spec parsing -> SpecModel.

Reuses the regex-based helpers in post2exe/gen_test_post.py (zero external deps,
proven on the whole dataset). We do NOT re-implement parsing.
"""
from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

from .config import REPO_ROOT
from .repo import Problem

# Make the post2exe helpers importable.
_POST2EXE = str(REPO_ROOT / "post2exe")
if _POST2EXE not in sys.path:
    sys.path.append(_POST2EXE)


import gen_test_post as gtp  # noqa: E402


@dataclass
class Param:
    name: str
    rust_type: str             # verbatim, e.g. "Vec<i32>", "&mut Vec<i32>", "i32"
    is_mut_ref: bool = False


@dataclass
class GenError:
    reason: str
    detail: str = ""

    def __bool__(self) -> bool:  # so callers can do `if isinstance(m, GenError)`
        return False


@dataclass
class SpecModel:
    problem_id: str
    kind: str
    fn_name: str
    params: list[Param]
    ret_name: str
    ret_type: str
    requires: list[str]
    ensures: list[str]
    returns_expr: str | None                 # `returns <expr>` form, if used
    helper_spec_fns: dict[str, str]          # name -> full text (transitive closure)
    consts: list[str]
    uses: list[str]

    @property
    def has_mut_ref(self) -> bool:
        return any(p.is_mut_ref for p in self.params)


_MUT_REF_RE = re.compile(r"^&\s*mut\s+")


def _trim_helper(text: str) -> str:
    """gtp.extract_spec_fns can over-capture a spec fn's text into the following
    function (its body-brace scan grabs the last brace in the block). Trim to the
    single fn: bound the body search to before the next fn head, so the body's
    matching close brace is found correctly.
    """
    m = re.search(gtp.FN_HEAD_RE, text)
    if not m:
        return text
    close_paren = gtp.find_matching_paren(text, m.end() - 1)
    if close_paren == -1:
        return text
    # Find the next fn head after this one (bounds the body region).
    nxt = None
    for mm in re.finditer(gtp.FN_HEAD_RE, text):
        if mm.start() > close_paren:
            nxt = mm.start()
            break
    region = text[:nxt] if nxt is not None else text
    body_open, body_close = gtp.find_fn_body_brace(region, close_paren + 1)
    if body_open == -1 or body_close == -1:
        return text[:nxt] if nxt is not None else text
    # Keep from the start of `text` (extract_spec_fns already begins at the
    # `pub [open|closed] spec fn` declaration); only trim the over-captured end.
    return text[:body_close + 1]


def _param_from_arg(name: str, rust_type: str) -> Param:
    rt = rust_type.strip()
    is_mut = bool(_MUT_REF_RE.match(rt))
    return Param(name=name.strip(), rust_type=rt, is_mut_ref=is_mut)


def load_spec_model(problem: Problem) -> SpecModel | GenError:
    """Parse spec.rs into a SpecModel, or return GenError on unsupported shapes."""
    spec_text = problem.read("spec.rs")
    if spec_text is None:
        return GenError("no_spec", "spec.rs missing")

    verus_text = gtp.extract_verus_block(spec_text)
    if not verus_text:
        return GenError("no_verus_block")

    fn_name, ensures, returns_expr = gtp.choose_target_fn(verus_text)
    if fn_name is None:
        return GenError("no_target_fn")

    # Signature (search the verus block; parse_signature finds the exec fn).
    try:
        sig = gtp.parse_signature(verus_text, fn_name)
    except ValueError as exc:
        return GenError("signature_parse", str(exc))

    if sig.receiver is not None:
        # &self / &mut self / self receivers: none in dataset per grounding.
        return GenError("receiver_unsupported", sig.receiver)

    params = [_param_from_arg(n, t) for (n, t) in sig.args]
    ret_name, ret_type = gtp.parse_return(sig.ret)

    requires = gtp.extract_requires_clauses(verus_text, fn_name)

    all_fns = gtp.extract_spec_fns(verus_text)
    needed = gtp.find_needed_spec_fns(ensures + requires, all_fns)
    helpers = {n: _trim_helper(all_fns[n]) for n in needed}

    consts = gtp.extract_const_lines(verus_text)
    uses = gtp.extract_use_lines(spec_text)

    return SpecModel(
        problem_id=problem.problem_id,
        kind=problem.kind,
        fn_name=fn_name,
        params=params,
        ret_name=ret_name,
        ret_type=ret_type,
        requires=requires,
        ensures=ensures,
        returns_expr=returns_expr,
        helper_spec_fns=helpers,
        consts=consts,
        uses=uses,
    )
