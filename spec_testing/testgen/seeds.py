"""Seed extraction from description.md examples.

Every problem ships worked examples with (Input, Output). These are free,
already-correct (input, output) pairs that (a) seed the generators and (b)
validate the whole driver chain (a seed must reproduce its stated output).
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field

from spec_testing.common.repo import Problem
from spec_testing.common.specmodel import SpecModel, GenError, load_spec_model


@dataclass
class Seed:
    input: dict | str          # LC: {param: value}; CF: raw stdin string
    output: object             # LC: value; CF: raw stdout string


@dataclass
class SeedResult:
    ok: bool
    seeds: list[Seed] = field(default_factory=list)
    error: str = ""


# ---------------------------------------------------------------------------
# Literal value parser (JSON-ish; handles the LeetCode example syntax)
# ---------------------------------------------------------------------------

class _LitParser:
    def __init__(self, text: str):
        self.s = text
        self.i = 0

    def _ws(self):
        while self.i < len(self.s) and self.s[self.i] in " \t":
            self.i += 1

    def parse(self):
        self._ws()
        v = self._value()
        return v

    def _value(self):
        self._ws()
        if self.i >= len(self.s):
            raise ValueError("empty value")
        c = self.s[self.i]
        if c == "[":
            return self._list()
        if c in "\"'":
            return self._string(c)
        if c == "{":
            return self._brace_list()
        return self._scalar()

    def _list(self):
        assert self.s[self.i] == "["
        self.i += 1
        out = []
        self._ws()
        if self.i < len(self.s) and self.s[self.i] == "]":
            self.i += 1
            return out
        while True:
            out.append(self._value())
            self._ws()
            if self.i >= len(self.s):
                raise ValueError("unterminated list")
            c = self.s[self.i]
            if c == ",":
                self.i += 1
                continue
            if c == "]":
                self.i += 1
                return out
            raise ValueError(f"unexpected {c!r} in list")

    def _brace_list(self):
        # Some problems write sets/arrays with {} — treat like a list.
        assert self.s[self.i] == "{"
        self.i += 1
        out = []
        self._ws()
        if self.i < len(self.s) and self.s[self.i] == "}":
            self.i += 1
            return out
        while True:
            out.append(self._value())
            self._ws()
            c = self.s[self.i] if self.i < len(self.s) else ""
            if c == ",":
                self.i += 1
                continue
            if c == "}":
                self.i += 1
                return out
            raise ValueError(f"unexpected {c!r} in brace-list")

    def _string(self, quote):
        self.i += 1
        buf = ""
        while self.i < len(self.s):
            c = self.s[self.i]
            if c == "\\" and self.i + 1 < len(self.s):
                buf += self.s[self.i + 1]
                self.i += 2
                continue
            if c == quote:
                self.i += 1
                return buf
            buf += c
            self.i += 1
        raise ValueError("unterminated string")

    def _scalar(self):
        start = self.i
        while self.i < len(self.s) and self.s[self.i] not in ",]}":
            self.i += 1
        tok = self.s[start:self.i].strip()
        return _scalar_from_token(tok)


def _scalar_from_token(tok: str):
    if tok in ("true", "True"):
        return True
    if tok in ("false", "False"):
        return False
    if tok in ("null", "None"):
        return None
    if re.fullmatch(r"-?\d+", tok):
        return int(tok)
    if re.fullmatch(r"-?\d+\.\d+", tok):
        return float(tok)
    # bare string (e.g. a single char or word)
    return tok


def parse_literal(text: str):
    return _LitParser(text.strip()).parse()


# ---------------------------------------------------------------------------
# Line normalization
# ---------------------------------------------------------------------------

# Prefix tolerates blockquote (`>`), list bullets (`-`, `*`, `+`) and bold
# markers — descriptions use both `> **Input:**` and `- **Input:** ...`
# styles.
_LABEL_RE = re.compile(
    r"^\s*(?:[>\-*+]\s*)*\*{0,2}\s*(Input|Output)\s*\*{0,2}\s*:\s*\*{0,2}\s*(.*)$",
    re.IGNORECASE)


def _clean_line(line: str) -> str:
    return line.rstrip("\n").rstrip()


def _split_kv_fragments(rhs: str) -> list[tuple[str, str]]:
    """Split `nums = [..], k = 2` into [(nums, [..]), (k, 2)] at top level."""
    parts: list[str] = []
    depth = 0
    cur = ""
    for ch in rhs:
        if ch in "[{(":
            depth += 1
        elif ch in "]})":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    out: list[tuple[str, str]] = []
    for p in parts:
        m = re.match(r"^\s*([A-Za-z_]\w*)\s*=\s*(.*)$", p, re.DOTALL)
        if m:
            out.append((m.group(1), m.group(2).strip()))
    return out


# ---------------------------------------------------------------------------
# LeetCode / extended extraction
# ---------------------------------------------------------------------------

def _snake(name: str) -> str:
    return re.sub(r"(?<=[a-z0-9])([A-Z])", r"_\1", name).lower()


def _canon_keys(d: dict, param_names: list[str]) -> dict:
    """Map description keys to spec parameter names. Descriptions use
    camelCase (`stoneValue`) while specs use snake_case (`stone_value`);
    a key is renamed only when it is not already a parameter and its
    snake_case form unambiguously is."""
    out = {}
    for k, v in d.items():
        if k not in param_names:
            sk = _snake(k)
            if sk in param_names and sk not in d:
                k = sk
        out[k] = v
    return out


def _extract_lc(text: str, model: SpecModel) -> SeedResult:
    param_names = [p.name for p in model.params]
    lines = text.splitlines()
    seeds: list[Seed] = []
    pending_input: dict | None = None
    errs: list[str] = []

    for line in lines:
        m = _LABEL_RE.match(_clean_line(line))
        if not m:
            continue
        label = m.group(1).lower()
        rhs = m.group(2).strip().strip("`").strip()
        if not rhs:
            continue
        if label == "input":
            frags = _split_kv_fragments(rhs)
            try:
                if frags:
                    d = _canon_keys({name: parse_literal(val) for name, val in frags},
                                    param_names)
                else:
                    # single unnamed value; assign to sole param
                    if len(param_names) == 1:
                        d = {param_names[0]: parse_literal(rhs)}
                    else:
                        raise ValueError("unnamed multi-param input")
                pending_input = d
            except ValueError as exc:
                errs.append(f"input parse: {exc}")
                pending_input = None
        elif label == "output":
            if pending_input is None:
                continue
            try:
                out_val = parse_literal(rhs)
            except ValueError as exc:
                errs.append(f"output parse: {exc}")
                pending_input = None
                continue
            seeds.append(Seed(input=pending_input, output=out_val))
            pending_input = None

    if not seeds:
        return SeedResult(ok=False, error="; ".join(errs) or "no examples parsed")
    return SeedResult(ok=True, seeds=seeds, error="; ".join(errs))


# ---------------------------------------------------------------------------
# Codeforces extraction (raw stdin/stdout code fences)
# ---------------------------------------------------------------------------

def _extract_cf(text: str) -> SeedResult:
    seeds: list[Seed] = []
    # Pattern: **Input:** \n ```\n<...>\n``` \n **Output:** \n ```\n<...>\n```
    blocks = re.findall(
        r"\*{0,2}\s*Input\s*:?\s*\*{0,2}\s*`{3,}[^\n]*\n(.*?)\n`{3,}.*?"
        r"\*{0,2}\s*Output\s*:?\s*\*{0,2}\s*`{3,}[^\n]*\n(.*?)\n`{3,}",
        text, re.DOTALL | re.IGNORECASE,
    )
    for inp, out in blocks:
        seeds.append(Seed(input=inp.strip("\n"), output=out.strip("\n")))
    if not seeds:
        return SeedResult(ok=False, error="no CF example fences parsed")
    return SeedResult(ok=True, seeds=seeds)


def _align_cf_seeds(raw: SeedResult, model: SpecModel) -> SeedResult:
    """Typed seeds from raw CF-style (stdin, stdout) examples via cf_align.
    Only cleanly-aligned examples are kept — never guessed."""
    from spec_testing.common.cf_align import align_cf_input, _parse_cf_output
    seeds: list[Seed] = []
    for s in raw.seeds:
        a = align_cf_input(model, s.input)
        if not a.ok:
            continue
        out = _parse_cf_output(str(s.output), model.ret_type)
        if out is None:
            continue
        seeds.append(Seed(input=a.values, output=out))
    if not seeds:
        return SeedResult(ok=False, error="cf examples found but none aligned")
    return SeedResult(ok=True, seeds=seeds)


def _extract_cf_structured(desc: str, problem: Problem, model: SpecModel) -> SeedResult | None:
    from spec_testing.common import cf_io
    raw = _extract_cf(desc)
    if not raw.ok:
        return None
    seeds: list[Seed] = []
    for s in raw.seeds:
        try:
            inps = cf_io.parse_stdin_generic(model, str(s.input))
            outs = cf_io.parse_stdout_cases_generic(model, str(s.output), len(inps))
            if len(inps) == len(outs) and inps:
                for inp_dict, out_val in zip(inps, outs):
                    seeds.append(Seed(input=inp_dict, output=out_val))
        except Exception:
            continue
    if seeds:
        return SeedResult(ok=True, seeds=seeds)
    return None


def extract_seeds(problem: Problem, model: SpecModel | None = None) -> SeedResult:
    desc = problem.read("description.md")
    if desc is None:
        return SeedResult(ok=False, error="no description.md")
    if problem.is_codeforces:
        if model is None:
            m = load_spec_model(problem)
            model = None if isinstance(m, GenError) else m
        if model is not None:
            struct_res = _extract_cf_structured(desc, problem, model)
            if struct_res is not None and struct_res.ok:
                return struct_res
        return _extract_cf(desc)
    if model is None:
        m = load_spec_model(problem)
        if isinstance(m, GenError):
            return SeedResult(ok=False, error=f"spec: {m.reason}")
        model = m
    r = _extract_lc(desc, model)
    if not r.seeds:
        # extended cf-ports keep CF-style fenced raw examples with an LC-style
        # signature: extract the fences, then align tokens to typed params
        raw = _extract_cf(desc)
        if raw.ok:
            aligned = _align_cf_seeds(raw, model)
            if aligned.ok:
                return aligned
            r = SeedResult(ok=False, error=(r.error + "; " + aligned.error).strip("; "))
    return r
