"""Generic, signature-based Codeforces stdin/stdout I/O encoders and decoders.

Dynamically translates between structured parameter dictionaries/values and raw
Codeforces stdin/stdout streams based on the problem's Verus SpecModel signature.
Fully generic across Codeforces problems with zero hardcoded problem IDs.

These are best-effort heuristics: they infer a problem's I/O shape from the
signature, which cannot always match a hand-written `main()` (e.g. digit- or
character-encoded vectors). They are the FALLBACK path. The primary path is the
arg-capture driver (see testgen/codegen.build_cf_capture_main), which reads the
exact typed values the real `main()` passes to the verified function; these
encoders/decoders are used only when capture is unavailable (e.g. no native
linker) and for the round-trip faithfulness check in casegen._ref_output.
"""
from __future__ import annotations

import re
from typing import Any, TYPE_CHECKING

if TYPE_CHECKING:
    from spec_testing.common.specmodel import SpecModel


def _join_ints(xs: list) -> str:
    return " ".join(str(int(x)) for x in xs)


_FALSE_TOKENS = {"0", "false", "False", "FALSE", "no", "No", "NO"}


def is_cf_io_supported(pid: str) -> bool:
    """Always True for Codeforces problems (generic dynamic I/O support)."""
    return True


def parse_stdin_generic(model: SpecModel, stdin: str) -> list[dict[str, Any]]:
    """Parse raw stdin (single or multi-case) into a list of structured parameter dicts.
    
    Uses SpecModel parameter types and names to dynamically map stdin tokens to arguments.
    """
    from spec_testing.common.values import spec_type

    toks = stdin.split()
    if not toks:
        return []

    params = model.params
    if not params:
        return []

    # Count scalar parameters in model signature
    num_scalars = sum(1 for p in params if spec_type(p.rust_type).kind in ("int", "bool"))

    # Detect multi-case count 't' vs single-case dimension parameter 'n'.
    t = 1
    idx = 0
    try:
        first_val = int(toks[0])
        if first_val > 0:
            if len(toks) - num_scalars == first_val or (len(toks) - num_scalars) % first_val == 0:
                t = 1
                idx = 0
            elif first_val > 1 and len(toks) > first_val:
                t = first_val
                idx = 1
    except ValueError:
        t = 1
        idx = 0

    # Classify parameters into scalars vs sequences/complex for order-independent parsing
    scalar_params = [p for p in params if spec_type(p.rust_type).kind in ("int", "bool")]
    seq_params = [p for p in params if spec_type(p.rust_type).kind not in ("int", "bool")]

    cases: list[dict[str, Any]] = []

    for _ in range(t):
        if idx >= len(toks):
            break

        case_dict: dict[str, Any] = {}
        dims: dict[str, int] = {}

        # 1. Parse scalar parameters FIRST (e.g. n, m, k) from the beginning of the case stream.
        # Competitive programming stdin always passes dimension scalars before vector payloads.
        for p in scalar_params:
            if idx >= len(toks):
                break
            st = spec_type(p.rust_type)
            if st.kind == "int":
                try:
                    val = int(toks[idx])
                    idx += 1
                    case_dict[p.name] = val
                    dims[p.name] = val
                except ValueError:
                    break
            elif st.kind == "bool":
                val = toks[idx] not in _FALSE_TOKENS
                idx += 1
                case_dict[p.name] = val

        # 2. Parse sequence/vector parameters (e.g. p, a, l, r, grid)
        # Check if we have dual vector parameters (e.g. l: Vec<i64>, r: Vec<i64>) with interleaved pairs (l_i, r_i)
        is_dual_vec_pairs = (
            len(seq_params) == 2
            and spec_type(seq_params[0].rust_type).kind == "seq"
            and spec_type(seq_params[1].rust_type).kind == "seq"
            and "n" in dims
            and len(toks) - idx >= 2 * dims["n"]
        )

        if is_dual_vec_pairs:
            n_len = dims["n"]
            vec1: list[int] = []
            vec2: list[int] = []
            for _ in range(n_len):
                if idx + 1 < len(toks):
                    try:
                        vec1.append(int(toks[idx]))
                        vec2.append(int(toks[idx + 1]))
                        idx += 2
                    except ValueError:
                        break
            case_dict[seq_params[0].name] = vec1
            case_dict[seq_params[1].name] = vec2

        else:
            for p in seq_params:
                if idx >= len(toks):
                    break
                st = spec_type(p.rust_type)

                if st.kind == "seq":
                    inner_kind = st.inner.kind if st.inner else "int"

                    # 2D Grid of characters (Vec<Vec<char>> / Vec<String>)
                    if st.inner and st.inner.kind == "seq":
                        n_rows = dims.get("n", dims.get("len", 1))
                        grid: list[list[int]] = []
                        for _ in range(n_rows):
                            if idx < len(toks):
                                row_str = toks[idx]
                                idx += 1
                                # Map '#' -> 1, '.' -> 0, or ascii ords
                                row_vals = [1 if ch == "#" else (0 if ch == "." else ord(ch)) for ch in row_str]
                                grid.append(row_vals)
                        case_dict[p.name] = grid

                    elif inner_kind == "char":
                        # String or Vec<char>
                        val_str = toks[idx]
                        idx += 1
                        case_dict[p.name] = val_str

                    else:
                        # Determine 1D vector length
                        vec_len = None
                        for d_key in ("n", "len", "size", "k", "m"):
                            if d_key in dims and dims[d_key] > 0:
                                vec_len = dims[d_key]
                                break

                        if vec_len is None:
                            if idx < len(toks) and toks[idx].isdigit():
                                cand = int(toks[idx])
                                if cand > 0 and len(toks) - (idx + 1) >= cand:
                                    vec_len = cand
                                    idx += 1

                        if vec_len is None or vec_len <= 0:
                            vec_len = len(toks) - idx

                        if inner_kind == "tuple":
                            tuple_len = len(st.inner.elems) if st.inner and st.inner.elems else 2
                            tuples: list[tuple] = []
                            for _ in range(vec_len):
                                if idx + tuple_len <= len(toks):
                                    try:
                                        tup = tuple(int(toks[idx + i]) for i in range(tuple_len))
                                        tuples.append(tup)
                                        idx += tuple_len
                                    except ValueError:
                                        break
                            case_dict[p.name] = tuples
                        else:
                            arr: list[int] = []
                            for _ in range(vec_len):
                                if idx < len(toks):
                                    try:
                                        arr.append(int(toks[idx]))
                                        idx += 1
                                    except ValueError:
                                        break
                            case_dict[p.name] = arr

                elif st.kind == "tuple":
                    elem_count = len(st.elems) if st.elems else 2
                    tup_vals = [int(toks[idx + i]) for i in range(elem_count) if idx + i < len(toks)]
                    idx += elem_count
                    case_dict[p.name] = tup_vals

        if len(case_dict) == len(params):
            cases.append(case_dict)

    return cases


def build_stdin_generic(model: SpecModel, inp: dict[str, Any]) -> str:
    """Serialize a structured input parameter dict into single-case (t=1) CF stdin string.
    
    Formats scalars on line 1, vectors/matrices on subsequent lines.
    """
    from spec_testing.common.values import spec_type

    scalars: list[str] = []
    vectors: list[str] = []

    for p in model.params:
        if p.name not in inp:
            continue
        val = inp[p.name]
        st = spec_type(p.rust_type)

        if st.kind in ("int", "bool"):
            scalars.append(str(int(val) if isinstance(val, bool) else val))

        elif st.kind == "seq":
            inner_kind = st.inner.kind if st.inner else "int"
            if inner_kind == "char":
                scalars.append(str(val))
            elif inner_kind == "tuple" and isinstance(val, list):
                lines = []
                for tup in val:
                    lines.append(" ".join(str(x) for x in tup))
                vectors.append("\n".join(lines))
            elif isinstance(val, list):
                vectors.append(_join_ints(val))

        elif st.kind == "tuple" and isinstance(val, (list, tuple)):
            scalars.append(" ".join(str(x) for x in val))

    lines: list[str] = ["1"]  # t=1 header for single-case execution
    if scalars:
        lines.append(" ".join(scalars))
    for v in vectors:
        lines.append(v)

    return "\n".join(lines) + "\n"


def parse_stdout_generic(model: SpecModel, stdout: str) -> Any:
    """Parse raw stdout into a typed return value based on model.ret_type."""
    from spec_testing.common.values import spec_type

    toks = stdout.split()
    if not toks:
        return None

    st = spec_type(model.ret_type)

    if st.kind == "bool":
        return toks[0] not in _FALSE_TOKENS

    if st.kind == "int":
        try:
            return int(toks[0])
        except ValueError:
            return None

    if st.kind == "seq":
        # A CF answer line is the bare sequence of values. Do NOT treat the first
        # token as a length prefix: competitive outputs print the answer directly,
        # and the old `len(toks) == toks[0] + 1` guess corrupted any sequence whose
        # first value happened to equal (len - 1) — e.g. the permutation "1 2" was
        # read as [2] instead of [1, 2] (cf136A). A genuine count prefix, when it
        # exists, sits on its own line and is handled by parse_stdout_cases_generic.
        try:
            return [int(x) for x in toks]
        except ValueError:
            return None

    if st.kind == "tuple":
        try:
            return [int(x) for x in toks]
        except ValueError:
            return None

    return None


def parse_stdout_cases_generic(model: SpecModel, stdout: str, n_cases: int) -> list[Any]:
    """Parse raw stdout containing n_cases answers into a list of typed values."""
    if n_cases <= 1:
        v = parse_stdout_generic(model, stdout)
        return [v] if v is not None else []

    lines = [ln.strip() for ln in stdout.strip().splitlines() if ln.strip()]
    if len(lines) == n_cases:
        out = []
        for line in lines:
            v = parse_stdout_generic(model, line)
            if v is None:
                return []
            out.append(v)
        return out

    toks = stdout.split()
    if len(toks) == n_cases:
        out = []
        for tok in toks:
            v = parse_stdout_generic(model, tok)
            if v is None:
                return []
            out.append(v)
        return out

    return []
