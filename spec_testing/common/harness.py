"""Verus harness rendering: seq-level postcondition rewrite + proof-fn files. Shared by the precondition gate and the symbolic probes.

The rewrite turns the ground-truth `ensures`/`requires` clauses (written over
Vec/String/&mut exec types) into spec functions `__vc_post`/`__vc_pre` written
over Seq/int, so the verifier can evaluate them on concrete literals.
"""
from __future__ import annotations

import re
from dataclasses import dataclass

from .specmodel import SpecModel
from .values import SpecType, render_value, spec_type

_IDENT = r"[A-Za-z_][A-Za-z0-9_]*"


@dataclass
class SpecParam:
    """A spec-level parameter of __vc_post/__vc_pre."""
    name: str            # possibly renamed (__old_p / __new_p) for &mut
    st: SpecType
    origin: str          # the original param name it derives from
    role: str = "value"  # value|old|new|ret


def spec_params(model: SpecModel, shallow: bool = False) -> list[SpecParam]:
    """Expand model params to spec params (&mut -> __old_/__new_ pair).

    shallow=True: symbolic-probe type mapping (values.spec_type_shallow) —
    Vec<Vec<T>> stays Seq<Vec<T>> so problem helpers type-check; only valid
    when no concrete literals are rendered."""
    from .values import spec_type_shallow
    map_t = spec_type_shallow if shallow else spec_type
    out: list[SpecParam] = []
    for p in model.params:
        if p.is_mut_ref:
            elem = map_t(p.rust_type)  # Seq<T> after ref strip
            out.append(SpecParam(name=f"__old_{p.name}", st=elem, origin=p.name, role="old"))
            out.append(SpecParam(name=f"__new_{p.name}", st=elem, origin=p.name, role="new"))
        else:
            out.append(SpecParam(name=p.name, st=map_t(p.rust_type), origin=p.name, role="value"))
    return out


def ret_spec_param(model: SpecModel, shallow: bool = False) -> SpecParam:
    from .values import spec_type_shallow
    map_t = spec_type_shallow if shallow else spec_type
    return SpecParam(name=model.ret_name, st=map_t(model.ret_type), origin=model.ret_name, role="ret")


# ---------------------------------------------------------------------------
# Clause rewriting
# ---------------------------------------------------------------------------

def _strip_view_sigils(text: str, roots: list[str]) -> str:
    """Strip `@` view sigils rooted at a param/ret name.

    Iteratively: `q@` -> `q` for each root, and `]@` -> `]`. On ambiguity we
    leave text unchanged; a downstream compile error will catch mistakes.
    """
    # root@  ->  root
    for r in roots:
        text = re.sub(rf"\b{re.escape(r)}@", r, text)
    # ]@ -> ]  (closes an index/call chain that began at a root)
    text = text.replace("]@", "]")
    return text


def rewrite_clause(clause: str, model: SpecModel, context: str = "ensures") -> str:
    """Rewrite one ensures/requires clause to the seq level.

    context 'requires': bare &mut names denote the PRE-state (requires are
    evaluated at fn entry, where `old()` does not exist); in ensures a bare
    &mut name denotes the POST-state.
    """
    text = clause

    # Step 2: &mut param renaming.
    for p in model.params:
        if not p.is_mut_ref:
            continue
        text = re.sub(rf"\bold\s*\(\s*{re.escape(p.name)}\s*\)", f"__old_{p.name}", text)
        text = re.sub(rf"\bfinal\s*\(\s*{re.escape(p.name)}\s*\)", f"__new_{p.name}", text)
        # Remaining bare name -> pre-state in requires, post-state in ensures.
        repl = f"__old_{p.name}" if context == "requires" else f"__new_{p.name}"
        text = re.sub(rf"\b{re.escape(p.name)}\b", repl, text)

    # Step 3: strip `@` view sigils rooted at params / ret / renamed params.
    roots = [p.name for p in model.params]
    roots += [model.ret_name]
    roots += [f"__old_{p.name}" for p in model.params if p.is_mut_ref]
    roots += [f"__new_{p.name}" for p in model.params if p.is_mut_ref]
    text = _strip_view_sigils(text, roots)

    # Step 4: everything else stays verbatim.
    return text.strip()


def _rewrite_returns_expr(model: SpecModel) -> str | None:
    if model.returns_expr is None:
        return None
    expr = rewrite_clause(model.returns_expr, model)
    return f"{model.ret_name} == ({expr})"


def _param_decl(sp: SpecParam) -> str:
    return f"{sp.name}: {sp.st}"


def build_pre_fn(model: SpecModel, shallow: bool = False) -> str:
    sps = spec_params(model, shallow)
    decls = ", ".join(_param_decl(sp) for sp in sps)
    if model.requires:
        body = "\n".join(f"    &&& ({rewrite_clause(c, model, 'requires')})"
                         for c in model.requires)
    else:
        body = "    &&& true"
    text = f"pub open spec fn __vc_pre({decls}) -> bool {{\n{body}\n}}"
    return rewrite_self_calls(text)


def build_post_fn(model: SpecModel, shallow: bool = False) -> str:
    sps = spec_params(model, shallow)
    rp = ret_spec_param(model, shallow)
    decls = ", ".join(_param_decl(sp) for sp in sps + [rp])

    clauses: list[str] = []
    ret_clause = _rewrite_returns_expr(model)
    if ret_clause is not None:
        clauses.append(ret_clause)
    for c in model.ensures:
        clauses.append(rewrite_clause(c, model))

    if not clauses:
        body = "    &&& true"
    else:
        body = "\n".join(f"    &&& ({c})" for c in clauses)
    text = f"pub open spec fn __vc_post({decls}) -> bool {{\n{body}\n}}"
    return rewrite_self_calls(text)


# ---------------------------------------------------------------------------
# Helper spec fns (transitive closure) with Self:: -> Solution:: rewrite
# ---------------------------------------------------------------------------

def _uses_self(model: SpecModel) -> bool:
    for t in model.helper_spec_fns.values():
        if "Self::" in t or "Solution::" in t:
            return True
    for c in model.ensures + model.requires:
        if "Self::" in c or "Solution::" in c:
            return True
    return False


def render_helpers(model: SpecModel) -> tuple[str, bool]:
    """Return (helper_text, uses_impl). If helpers are impl-scoped (Self::),
    wrap them in `impl Solution { ... }` and the caller rewrites Self:: in
    posts. Spec consts are also declared inside the impl so `Self::<CONST>`
    references resolve (callers additionally render them at top level for
    unqualified references — the two declarations coexist)."""
    if not model.helper_spec_fns and not (model.consts and _uses_self(model)):
        return "", False
    uses_impl = _uses_self(model)
    body = "\n\n".join(model.helper_spec_fns.values())
    if uses_impl:
        consts = "\n".join(f"pub {c}" if c.lstrip().startswith("const") else c
                           for c in model.consts)
        inner = (consts + "\n\n" if consts else "") + body
        return f"pub struct Solution;\nimpl Solution {{\n{inner}\n}}", True
    return body, False


def rewrite_self_calls(text: str) -> str:
    return text.replace("Self::", "Solution::")


def render_uses(model: SpecModel) -> str:
    """Non-prelude `use` lines from the spec, for harness file headers.

    Spec helpers may reference vstd items beyond the prelude; every rendered
    probe file must carry the spec's own imports or the helpers fail to
    compile.
    """
    out: list[str] = []
    for u in model.uses:
        u = u.strip()
        if not u or "vstd::prelude" in u:
            continue
        if u not in out:
            out.append(u)
    return "\n".join(out)


def recursive_helper_names(model: SpecModel) -> set[str]:
    """Helper spec fns that are actually (mutually) recursive.

    `decreases` alone is not enough: Verus rejects reveal_with_fuel(f, n>1) on
    a non-recursive fn (vir_error), and a helper may carry `decreases`
    without being self-recursive.
    """
    bodies: dict[str, str] = {}
    for name, text in model.helper_spec_fns.items():
        brace = text.find("{")
        bodies[name] = text[brace:] if brace != -1 else text
    calls: dict[str, set[str]] = {
        a: {b for b in bodies if re.search(rf"\b{re.escape(b)}\s*\(", body)}
        for a, body in bodies.items()
    }
    out: set[str] = set()
    for start in bodies:
        seen: set[str] = set()
        frontier = set(calls.get(start, ()))
        while frontier:
            cur = frontier.pop()
            if cur == start:
                out.add(start)
                break
            if cur in seen:
                continue
            seen.add(cur)
            frontier |= calls.get(cur, set())
    return out


# vstd spec fns that are recursive (fuel-gated) and commonly referenced by
# dataset specs. `pow2` itself is non-recursive (reveal_with_fuel on it is a
# vir_error) — its recursion lives in `pow`, so both map to pow's path.
_VSTD_FUEL_FNS = {
    "pow2": "vstd::arithmetic::power::pow",
    "pow": "vstd::arithmetic::power::pow",
}


def vstd_fuel_paths(model: SpecModel) -> list[str]:
    """Fuel-gated vstd fns referenced by the post or the problem helpers —
    without a reveal_with_fuel these leave ground terms like pow(2, 3)
    undecided at any rlimit."""
    text = "\n".join(model.ensures) + "\n" + (model.returns_expr or "") + "\n" + \
        "\n".join(model.helper_spec_fns.values())
    out: list[str] = []
    for name, path in _VSTD_FUEL_FNS.items():
        if re.search(rf"\b{name}\s*\(", text) and path not in out:
            out.append(path)
    return out


def recursive_helper_paths(model: SpecModel) -> list[str]:
    """Solution::-qualified paths (when impl-scoped) for reveal_with_fuel."""
    rec = recursive_helper_names(model)
    uses_self = _uses_self(model)
    out = [f"Solution::{n}" if uses_self else n
           for n, t in model.helper_spec_fns.items() if n in rec and "decreases" in t]
    return out + vstd_fuel_paths(model)


# ---------------------------------------------------------------------------
# Concrete `let` bindings + mechanical ground hints
# ---------------------------------------------------------------------------

def render_lets(sps_with_vals: list[tuple[SpecParam, object]]) -> list[str]:
    lets: list[str] = []
    for sp, val in sps_with_vals:
        lets.append(f"let {sp.name}: {sp.st} = {render_value(val, sp.st)};")
    return lets


def _seq_hints(name: str, val, st: SpecType, hint_cap: int) -> list[str]:
    """Plant ground trigger terms for a seq-typed value."""
    hints: list[str] = []
    if st.kind == "seq" and isinstance(val, list):
        hints.append(f"assert({name}.len() == {len(val)});")
        for k, elem in enumerate(val[:hint_cap]):
            if st.inner and st.inner.kind == "int":
                hints.append(f"assert({name}[{k}] == {elem}{st.inner.rust_name});")
    elif st.kind == "seq" and isinstance(val, str):  # Seq<char>
        hints.append(f"assert({name}.len() == {len(val)});")
    return hints


def compute_fuel(values: list) -> int:
    """Fuel for reveal_with_fuel over the concrete case values.

    Recursion depth of a helper may be driven by a SCALAR argument, not only
    by sequence lengths — take the max over both, capped. Nested lists
    contribute their max inner length too.
    """
    cap = int(model_fuel_cap())
    depth = 0
    # Scalars contribute at most 64: an unrelated large scalar (target=10000)
    # must not inflate fuel to the cap for every recursive-helper problem, and
    # scalar-driven recursion deeper than ~64 is unprovable in practice anyway
    # (labeled reason "fuel_hard" by the symbolic stage).
    scalar_cap = min(64, cap)

    def _feed(v):
        nonlocal depth
        if isinstance(v, bool) or v is None:
            return
        if isinstance(v, int):
            depth = max(depth, min(abs(v), scalar_cap))
        elif isinstance(v, (list, str)):
            depth = max(depth, len(v))
            if isinstance(v, list):
                for e in v:
                    _feed(e)
        elif isinstance(v, dict):
            for e in v.values():
                _feed(e)

    for v in values:
        _feed(v)
    return min(depth + 1, cap)


_STRLIT_RE = re.compile(r'"(?:[^"\\]|\\.)*"')

# Trigger annotations in both attribute forms — `#[trigger]` and
# `#![trigger expr[i]]` / `#![auto]` (one bracket-nesting level) — are only
# legal inside a quantifier; instantiated bodies must shed them.
TRIGGER_ATTR_RE = re.compile(r"#!?\[\s*(?:trigger|auto)(?:[^\[\]]|\[[^\]]*\])*\]\s*")


def strlit_hints(model: SpecModel) -> list[str]:
    """reveal_strlit for every string literal in the spec clauses — the view
    of a string literal (`"Alice"@`) is opaque to Z3 until revealed."""
    text = "\n".join(model.ensures + model.requires) + "\n" + \
        (model.returns_expr or "") + "\n".join(model.helper_spec_fns.values())
    out: list[str] = []
    for m in _STRLIT_RE.finditer(text):
        h = f"reveal_strlit({m.group(0)});"
        if h not in out:
            out.append(h)
    return out[:8]


_BIT_WIDTH = {"i8": 8, "i16": 16, "i32": 32, "i64": 64, "i128": 128,
              "u8": 8, "u16": 16, "u32": 32, "u64": 64, "u128": 128,
              "usize": 64, "isize": 64}
_BITOP_RE = re.compile(r"\b(\w+)\s*(\^|&(?!&)|\|(?!\|))\s*(\w+)\b")


def _bitop_value(a: int, b: int, op: str, ty: str) -> int:
    """Two's-complement-correct ^ & | for the given machine-int type."""
    width = _BIT_WIDTH[ty]
    mask = (1 << width) - 1
    av, bv = a & mask, b & mask
    r = av ^ bv if op == "^" else (av & bv if op == "&" else av | bv)
    if ty.startswith("i") and r >= 1 << (width - 1):
        r -= 1 << width
    return r


def bitop_hints(model: SpecModel, values: dict) -> list[str]:
    """Grounding facts for bitwise expressions over int parameters.

    Plain SMT has no bitvector theory for integer `^`/`&`/`|` and the
    computation prover does not reduce them, so a clause like
    `popcnt((start ^ goal) as nat)` is undecidable on concrete cases without
    help. For each such expression whose operands have concrete values, the
    result is computed here and asserted through a self-contained
    `by (bit_vector)` side-proof (its `requires` carries the operand values —
    bit_vector queries do not see the surrounding context).
    """
    types = {p.name: p.rust_type.strip() for p in model.params}
    types[model.ret_name] = model.ret_type.strip()
    text = "\n".join(model.ensures + model.requires) + "\n" + \
        (model.returns_expr or "") + "\n".join(model.helper_spec_fns.values())
    out: list[str] = []
    seen: set[tuple] = set()
    for m in _BITOP_RE.finditer(text):
        lhs, op, rhs = m.group(1), m.group(2), m.group(3)

        def _operand(tok):
            if tok in values and types.get(tok) in _BIT_WIDTH and \
                    isinstance(values[tok], int) and not isinstance(values[tok], bool):
                return values[tok], types[tok]
            if re.fullmatch(r"\d+", tok):
                return int(tok), None
            return None, None

        av, at = _operand(lhs)
        bv, bt = _operand(rhs)
        ty = at or bt
        if av is None or bv is None or ty is None:
            continue
        key = (lhs, op, rhs)
        if key in seen:
            continue
        seen.add(key)
        r = _bitop_value(av, bv, op, ty)
        reqs = ", ".join(f"{tok} == {val}{ty}"
                         for tok, val, t in ((lhs, av, at), (rhs, bv, bt)) if t)
        out.append(f"assert({lhs} {op} {rhs} == {r}{ty}) by (bit_vector)\n"
                   f"            requires {reqs};")
        if len(out) >= 8:
            break
    return out


def strlit_ext_hints(model: SpecModel, ret_expr: str) -> list[str]:
    """Ghost `=~=` bindings between a sequence-typed return value and each
    spec string literal. Proving seq equality needs the extensionality axiom
    triggered; disproving it does not — without these, literal-comparison
    posts reject but never accept."""
    from .values import spec_type
    st = spec_type(model.ret_type)
    if not (st.kind == "seq" and st.inner is not None and st.inner.kind == "char"):
        return []
    # helper bodies too: the candidate literals may live inside a spec fn the
    # ensures delegates to
    text = "\n".join(model.ensures) + "\n" + (model.returns_expr or "") + \
        "\n".join(model.helper_spec_fns.values())
    out: list[str] = []
    seen: set[str] = set()
    for m in _STRLIT_RE.finditer(text):
        lit = m.group(0)
        if lit in seen:
            continue
        seen.add(lit)
        out.append(f"let _strext_{len(out)} = ({ret_expr} =~= {lit}@);")
    return out[:8]


def render_hints(sps_with_vals: list[tuple[SpecParam, object]], model: SpecModel, hint_cap: int) -> list[str]:
    hints: list[str] = []
    # reveal_with_fuel only for genuinely recursive helpers (vir_error otherwise).
    fuel = compute_fuel([val for _, val in sps_with_vals])
    for path in recursive_helper_paths(model):
        hints.append(f"reveal_with_fuel({path}, {fuel});")
    hints += strlit_hints(model)
    for sp, val in sps_with_vals:
        hints += _seq_hints(sp.name, val, sp.st, hint_cap)
    return hints


def model_fuel_cap() -> int:
    from .config import get
    return int(get("harness", "fuel_cap", 200))


# ---------------------------------------------------------------------------
# Existential ground-term saturation
#
# `exists|i: int, j: int| ... helper(x, i, j) ...` posts are unprovable on
# concrete cases when no ground helper terms exist for Z3's quantifier
# triggers to match. For small cases we instantiate the exists BODY over the
# index grid via ghost let bindings — `let _sat_k = (B);` plants every term
# of B as a ground term in the query (tautology asserts like
# `assert(B || !B)` are simplified away before Z3 sees them), letting Z3
# find the witness itself. Purely additive: never changes a verdict's
# meaning, only decidability.
# ---------------------------------------------------------------------------

_INT_BV_TYPES = {"int", "i8", "i16", "i32", "i64", "usize", "nat"}


def _trim_balanced(text: str) -> str:
    """Cut at the first unbalanced closing bracket (a quantifier body may sit
    inside an enclosing parenthesized expression)."""
    depth = 0
    for i, ch in enumerate(text):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth < 0:
                return text[:i]
    return text


def parse_quant_clauses(clause: str, keyword: str = "exists") -> list[tuple[list[tuple[str, str]], str]]:
    """[( [(var, type), ...], body )] for each `keyword |vars| body` in an
    (already-rewritten) clause. Bodies that themselves contain further
    quantifiers are skipped (the saturation caller handles only flat bodies)."""
    decl_re = re.compile(rf"\b{keyword}\s*\|([^|]*)\|")
    out = []
    for m in decl_re.finditer(clause):
        decl = m.group(1)
        bvs: list[tuple[str, str]] = []
        for part in decl.split(","):
            if ":" in part:
                name, ty = part.split(":", 1)
            else:
                name, ty = part, ""   # untyped binder: name still matters for scoping
            name = name.strip()
            if name:
                bvs.append((name, ty.strip()))
        if not bvs:
            continue
        body = _trim_balanced(clause[m.end():]).strip()
        if not body:
            continue
        if re.search(r"\b(forall|exists)\b", body):
            continue
        out.append((bvs, body))
    return out


def bv_literal(v: int, ty: str) -> str | None:
    """Typed spec literal for an int-kind bound-variable type, or None when
    the value is unrepresentable in that type."""
    from .values import _INT_RANGES
    if ty == "int":
        return f"{v}int"
    if ty == "nat":
        return None if v < 0 else f"{v}nat"
    if ty in _INT_RANGES:
        lo, hi = _INT_RANGES[ty]
        return f"{v}{ty}" if lo <= v <= hi else None
    return None


def _saturation_points(case_vals: list, max_points: int) -> list[int]:
    """Candidate instantiation values for int-bound quantifiers: the index
    range [0, n] (n = max container length) plus the distinct small scalar
    values occurring in the case (with each value's neighbourhood), since
    quantifiers may range over value domains — and quantified properties hold
    or break at the boundary values present in the input."""
    n = 0
    values: set[int] = set()

    def _feed(v):
        nonlocal n
        if isinstance(v, bool) or v is None:
            return
        if isinstance(v, int):
            if abs(v) <= 100_000:
                values.add(v)
        elif isinstance(v, (list, str)):
            n = max(n, len(v))
            if isinstance(v, list):
                for e in v:
                    _feed(e)
        elif isinstance(v, dict):
            for e in v.values():
                _feed(e)

    for v in case_vals:
        _feed(v)
    # priority order: the index range first (trimming drops from the end, and
    # index instantiations serve the common container-quantifier case), then
    # boundary values by magnitude
    pts = list(range(n + 1))
    seen = set(pts)
    for v in sorted(values, key=abs)[:max_points]:
        for cand in (v, v - 1, v + 1):
            if cand not in seen:
                seen.add(cand)
                pts.append(cand)
    return pts


def exists_saturation(clauses: list[str], case_vals: list, budget: int) -> list[str]:
    """Ghost bindings instantiating int-bound quantifier bodies over a
    candidate point set (container index range plus scalar values present in
    the case, shrunk to fit the budget). Covers `exists` bodies and
    quantifier-free `forall` bodies (including foralls nested inside an
    exists — argmax-style posts): the planted ground terms let Z3 both find
    witnesses and discharge bounded foralls. Empty when the clauses have no
    saturable quantifier."""
    from .config import get
    if not bool(get("harness", "exists_saturation", True)):
        return []
    points = _saturation_points(case_vals, max_points=12)
    if not points or points == [0]:
        return []
    import itertools
    hints: list[str] = []
    quant_sites: list[tuple[list[tuple[str, str]], str, set]] = []
    for clause in clauses:
        sites = (parse_quant_clauses(clause, "exists") +
                 parse_quant_clauses(clause, "forall"))
        # bound-variable names from EVERY binder decl in the clause — a site
        # dropped for having a nested body still binds names its inner sites
        # reference
        clause_bvs = {part.split(":")[0].strip()
                      for m in re.finditer(r"\b(?:exists|forall)\s*\|([^|]*)\|", clause)
                      for part in m.group(1).split(",") if part.strip()}
        for bvs, body in sites:
            # a nested site's body may reference an ENCLOSING quantifier's
            # bound variable — after substituting only this site's own
            # variables such a body is not closed; skip it
            others = clause_bvs - {name for name, _ in bvs}
            if any(re.search(rf"\b{re.escape(o)}\b", body) for o in others):
                continue
            quant_sites.append((bvs, body, others))
    for bvs, body, _ in quant_sites:
        if any(ty not in _INT_BV_TYPES for _, ty in bvs):
            continue
        body = TRIGGER_ATTR_RE.sub("", body)
        body = rewrite_self_calls(body)   # probes live outside impl Solution
        k = len(bvs)
        pts = list(points)
        while len(pts) > 2 and len(pts) ** k > max(1, budget - len(hints)):
            pts.pop()   # keep low values: index ranges first, then boundaries
        if len(pts) ** k > max(1, budget - len(hints)):
            continue
        for tup in itertools.product(pts, repeat=k):
            # typed literals: any expression valid for the bound variable is
            # valid for a literal of its exact type (bare literals mis-infer)
            lits = [bv_literal(v, ty) for (_, ty), v in zip(bvs, tup)]
            if any(l is None for l in lits):
                continue
            inst = body
            for (name, _), lit in zip(bvs, lits):
                inst = re.sub(rf"\b{re.escape(name)}\b", lit, inst)
            hints.append(f"let _sat_{len(hints)} = ({inst});")
    return hints[:budget]
