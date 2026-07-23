"""JSON testcase value <-> Verus spec-literal rendering + type substitution.

Pure functions, no I/O — the bulk is unit-tested in spec_testing/tests/.
"""
from __future__ import annotations

import re
from dataclasses import dataclass

# Integer types and their [min, max] ranges.
_INT_RANGES: dict[str, tuple[int, int]] = {
    "i8": (-(2**7), 2**7 - 1),
    "i16": (-(2**15), 2**15 - 1),
    "i32": (-(2**31), 2**31 - 1),
    "i64": (-(2**63), 2**63 - 1),
    "i128": (-(2**127), 2**127 - 1),
    "u8": (0, 2**8 - 1),
    "u16": (0, 2**16 - 1),
    "u32": (0, 2**32 - 1),
    "u64": (0, 2**64 - 1),
    "u128": (0, 2**128 - 1),
    # usize/isize: assume 64-bit target.
    "usize": (0, 2**64 - 1),
    "isize": (-(2**63), 2**63 - 1),
}
PRIMITIVE_INT = set(_INT_RANGES)


class ValueError_(Exception):
    """Raised by render_value on unrepresentable data (mapped to GEN_ERROR)."""


@dataclass
class SpecType:
    """A parsed spec-level type used for rendering literals."""
    kind: str                    # "int" | "bool" | "char" | "seq" | "option" | "tuple" | "opaque"
    inner: "SpecType | None" = None
    elems: "list[SpecType] | None" = None
    rust_name: str = ""          # original rust scalar name for ints (e.g. "i32")

    def __str__(self) -> str:
        if self.kind == "int":
            return self.rust_name
        if self.kind == "bool":
            return "bool"
        if self.kind == "char":
            return "char"
        if self.kind == "seq":
            return f"Seq<{self.inner}>"
        if self.kind == "option":
            return f"Option<{self.inner}>"
        if self.kind == "tuple":
            return "(" + ", ".join(str(e) for e in (self.elems or [])) + ")"
        return self.rust_name or "??"


def _strip_ref(t: str) -> str:
    t = t.strip()
    t = re.sub(r"^&\s*mut\s+", "", t)
    t = re.sub(r"^&\s*", "", t)
    return t.strip()


def _split_generic(inner: str) -> list[str]:
    """Split a generic arg list on top-level commas."""
    parts: list[str] = []
    depth = 0
    cur = ""
    for ch in inner:
        if ch in "<([":
            depth += 1
        elif ch in ">)]":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    return [p.strip() for p in parts]


def spec_type(rust_type: str) -> SpecType:
    """Map a Rust type to its spec-level representation.

    Vec<T>/&Vec<T> -> Seq<spec_type(T)>; String/&str -> Seq<char>;
    integers/bool/char unchanged; Option<T> -> Option<spec_type(T)>;
    tuples element-wise. &mut Vec<T> is handled by the caller (two params);
    here it maps to Seq<T> for the underlying element type.
    """
    t = _strip_ref(rust_type)

    if t in PRIMITIVE_INT or t in ("int", "nat"):
        return SpecType(kind="int", rust_name=("i64" if t in ("int", "nat") else t))
    if t == "bool":
        return SpecType(kind="bool")
    if t == "char":
        return SpecType(kind="char")

    if t in ("String", "str"):
        return SpecType(kind="seq", inner=SpecType(kind="char"))

    m = re.match(r"^(?:Vec|Seq)\s*<(.+)>$", t)
    if m:
        return SpecType(kind="seq", inner=spec_type(m.group(1)))

    m = re.match(r"^Option\s*<(.+)>$", t)
    if m:
        return SpecType(kind="option", inner=spec_type(m.group(1)))

    if t.startswith("(") and t.endswith(")"):
        elems = [spec_type(e) for e in _split_generic(t[1:-1])]
        return SpecType(kind="tuple", elems=elems)

    return SpecType(kind="opaque", rust_name=t)


def spec_type_shallow(rust_type: str) -> SpecType:
    """Shallow spec mapping for SYMBOLIC harnesses (no concrete literals):
    only the OUTER container becomes Seq, the element type stays verbatim
    (Vec<Vec<i32>> -> Seq<Vec<i32>>), so problem helper spec fns that take
    Seq<Vec<T>> type-check. Never use for rendering
    concrete values (inner Vec literals cannot be written in spec contexts).
    """
    t = _strip_ref(rust_type)
    m = re.match(r"^Vec\s*<(.+)>$", t)
    if m:
        inner = m.group(1).strip()
        ist = spec_type(inner)
        if ist.kind == "seq" or ist.kind == "opaque":
            return SpecType(kind="seq", inner=SpecType(kind="opaque", rust_name=inner))
        return SpecType(kind="seq", inner=ist)
    return spec_type(rust_type)


def _check_int_range(n: int, rust_name: str) -> None:
    if rust_name in _INT_RANGES:
        lo, hi = _INT_RANGES[rust_name]
        if not (lo <= n <= hi):
            raise ValueError_(f"value {n} out of range for {rust_name}")


def _esc_char(c: str) -> str:
    if c == "'":
        return "\\'"
    if c == "\\":
        return "\\\\"
    if c == "\n":
        return "\\n"
    if c == "\t":
        return "\\t"
    if c == "\r":
        return "\\r"
    return c


def render_value(value, st: SpecType) -> str:
    """Render a JSON value as a Verus spec literal for the given SpecType."""
    if st.kind == "int":
        if isinstance(value, bool) or not isinstance(value, int):
            raise ValueError_(f"expected int for {st.rust_name}, got {value!r}")
        _check_int_range(value, st.rust_name)
        return f"{value}{st.rust_name}"

    if st.kind == "bool":
        if not isinstance(value, bool):
            raise ValueError_(f"expected bool, got {value!r}")
        return "true" if value else "false"

    if st.kind == "char":
        if not isinstance(value, str) or len(value) != 1:
            raise ValueError_(f"expected 1-char string, got {value!r}")
        return f"'{_esc_char(value)}'"

    if st.kind == "seq":
        inner = st.inner
        assert inner is not None
        # String encoded as Python str -> Seq<char>
        if inner.kind == "char" and isinstance(value, str):
            if value == "":
                return "Seq::<char>::empty()"
            return "seq![" + ", ".join(f"'{_esc_char(c)}'" for c in value) + "]"
        if not isinstance(value, list):
            raise ValueError_(f"expected list for {st}, got {value!r}")
        if len(value) == 0:
            return f"Seq::<{inner}>::empty()"
        return "seq![" + ", ".join(render_value(v, inner) for v in value) + "]"

    if st.kind == "option":
        inner = st.inner
        assert inner is not None
        if value is None:
            return f"None::<{inner}>"
        return f"Some({render_value(value, inner)})"

    if st.kind == "tuple":
        elems = st.elems or []
        if not isinstance(value, list) or len(value) != len(elems):
            raise ValueError_(f"expected {len(elems)}-tuple, got {value!r}")
        return "(" + ", ".join(render_value(v, e) for v, e in zip(value, elems)) + ")"

    raise ValueError_(f"cannot render opaque type {st.rust_name!r}")


def coerce_ok(value, st: SpecType) -> bool:
    """True if `value` is renderable for `st` (schema/range gate, no exception)."""
    try:
        render_value(value, st)
        return True
    except ValueError_:
        return False
