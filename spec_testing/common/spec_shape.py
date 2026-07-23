"""Static spec-shape classification.

Two pure predicates over a SpecModel:

- needs_exec_harness: the seq-level rewrite is known-broken for this shape
  (nested containers map to Seq<Seq<T>> while the problem's own helper spec fns
  take Seq<Vec<T>>; ). Callers should render the exec-mode
  harness (common/exec_harness.py) instead of the __vc_post rewrite.

- l1_hard: proving `assert(__vc_post(concrete...))` (the acceptance side) is
  expected to be beyond Z3 regardless of rlimit: the post quantifies over an
  unbounded domain (a Seq-typed bound variable) or hides a recursive helper
  inside an existential body, so a witness/induction would be required. Such
  cases are labeled UNDECIDED with reason quant_hard, not harness failures.
"""
from __future__ import annotations

import re

from .specmodel import SpecModel
from .values import spec_type


_NESTED_RE = re.compile(r"(?:Vec|Seq)\s*<\s*(?:Vec|Seq|String)\b")
_QUANT_SEQ_RE = re.compile(r"\b(?:forall|exists)\s*\|[^|]*:\s*Seq\s*<")
_EXISTS_RE = re.compile(r"\bexists\s*\|")


def _st_is_nested(rust_type: str) -> bool:
    st = spec_type(rust_type)
    return st.kind == "seq" and st.inner is not None and st.inner.kind == "seq"


def needs_exec_harness(model: SpecModel) -> bool:
    """True when the seq-level rewrite cannot type-check for this problem."""
    for p in model.params:
        if _st_is_nested(p.rust_type):
            return True
    if _st_is_nested(model.ret_type):
        return True
    # Helper spec fns whose signatures keep exec container types (Seq<Vec<T>>,
    # Vec<T> params) clash with the rewritten Seq<Seq<T>> harness params.
    for text in model.helper_spec_fns.values():
        head = text.split("{", 1)[0]
        if _NESTED_RE.search(head) or re.search(r":\s*&?\s*Vec\s*<", head):
            return True
    return False


def _recursive_helper_names(model: SpecModel) -> set[str]:
    return {name for name, text in model.helper_spec_fns.items() if "decreases" in text}


def post_text(model: SpecModel) -> str:
    return "\n".join(model.ensures) + ("\n" + (model.returns_expr or ""))


def l1_hard(model: SpecModel) -> bool:
    """True when the acceptance probe is expected-unprovable by shape."""
    text = post_text(model)
    if _QUANT_SEQ_RE.search(text):
        return True
    # exists whose body calls a recursive helper: Z3 must both pick a witness
    # and unfold the recursion — empirically unprovable (lc1004).
    rec = _recursive_helper_names(model)
    if rec:
        for m in _EXISTS_RE.finditer(text):
            body = text[m.start():m.start() + 600]
            if any(re.search(rf"\b{re.escape(name)}\s*\(", body) for name in rec):
                return True
    return False
