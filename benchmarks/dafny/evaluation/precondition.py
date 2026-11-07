"""Check that a solution's precondition is equivalent to the reference's, by proof.

The spec tests run every positive testcase through the solution's precondition,
so they catch one that is too strong, but never one that is too weak: every
testcase input is valid. Here Dafny tries to prove both implications, over the
inputs the Verus parameter types can represent (`TypeOK`: the reference's
clauses after "implicit in Verus: the parameters' integer types"):

  AnsImpliesRef   TypeOK && solution's pre ==> reference's pre   (not too weak)
  RefImpliesAns   TypeOK && reference's pre ==> solution's pre   (not too strong)

The solution goes in `module Ans`, the reference spec in `module Ref`, and the
lemmas, with empty bodies, in `module PreCheck`. Both proved: the check passes.
Otherwise the precondition needs manual review; a failed proof does not mean the
preconditions differ, and the result lists the clauses Dafny could not derive.
"""

import os
import re
import subprocess

TYPES_COMMENT = "// implicit in Verus: the parameters' integer types"
LEMMAS = (("AnsImpliesRef", "solution_implies_reference"), ("RefImpliesAns", "reference_implies_solution"))


def balanced(text, i, open_, close):
    """The index just past the `close` that matches an `open_` before index i."""
    depth = 1
    while depth and i < len(text):
        depth += {open_: 1, close: -1}.get(text[i], 0)
        i += 1
    return i


def predicate(text, name):
    """(parameters, body) of `predicate name(...) { body }` in text, or (None, None).
    Parameters may have tuple types, `queries: seq<(nat, nat)>`."""
    m = re.search(rf"predicate\s+{re.escape(name)}\s*\(", text)
    if not m:
        return None, None
    i = balanced(text, m.end(), "(", ")")
    b = re.match(r"\s*\{", text[i:])
    if not b:
        return None, None
    j = balanced(text, i + b.end(), "{", "}")
    return text[m.end(): i - 1], text[i + b.end(): j - 1]


def split_params(params):
    out, depth, cur = [], 0, ""
    for ch in params:
        depth += ch in "<("
        depth -= ch in ">)"
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    return out + ([cur.strip()] if cur.strip() else [])


def check_file(solution, ref_spec, entry):
    """The Dafny file with both lemmas, or None if the reference has no precondition."""
    ref = ref_spec.split("// ===== method =====")[0]
    params, body = predicate(ref, entry + "_pre")
    if params is None:
        return None
    types = body.split(TYPES_COMMENT, 1)
    typeok = (types[1].strip().lstrip("&").strip() if len(types) == 2 else "") or "true"
    args = ", ".join(p.split(":")[0].strip() for p in split_params(params))
    lemmas = "\n\n".join(f"""  lemma {lem}({params})
    requires TypeOK({args}) && {a}.{entry}_pre({args})
    ensures {b}.{entry}_pre({args})
  {{}}""" for lem, a, b in (("AnsImpliesRef", "Ans", "Ref"), ("RefImpliesAns", "Ref", "Ans")))
    return f"""module Ans {{
{solution}
}}

module Ref {{
{ref}
}}

module PreCheck {{
  import Ans
  import Ref

  predicate TypeOK({params}) {{
    {typeok}
  }}

{lemmas}
}}
"""


def unproved_clauses(log):
    return re.findall(r"Related location: this proposition could not be proved\n\s*\|\n\s*\d+ \|\s*(.*)", log)


def check(dafny, solution, ref_spec, entry, d, time_limit, timeout):
    """{"status": "pass" | "review" | "error", per lemma "proved" / "not_proved", and
    the reference (or solution) clauses not derived}. Works in directory d."""
    text = check_file(solution, ref_spec, entry)
    if text is None:
        return {"status": "error", "reason": "the reference has no precondition"}
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "precondition_check.dfy"), "w") as f:
        f.write(text)
    res = {}
    for lem, key in LEMMAS:
        try:
            r = subprocess.run([dafny, "verify", "--allow-warnings", "--verification-time-limit", str(time_limit),
                                "--filter-symbol", f"PreCheck.{lem}", "precondition_check.dfy"],
                               capture_output=True, text=True, timeout=timeout, cwd=d)
            out = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            res[key] = "not_proved"
            continue
        if r.returncode == 0 and re.search(r"[1-9]\d* verified, 0 errors", out):
            res[key] = "proved"
        elif re.search(r"\b\d+ verified, [1-9]\d* errors?\b", out):
            res[key] = "not_proved"
            clauses = unproved_clauses(out)
            if clauses:
                res[key + "_clauses_not_derived"] = clauses[:10]
        elif re.search(r"\b\d+ verified, \d+ errors?, [1-9]\d* (time outs?|out of resource)\b", out):
            res[key] = "not_proved"            # the lemma timed out: not proved, so reviewed
            res[key + "_note"] = "timed out"
        else:
            return {"status": "error", "reason": f"{lem} did not check", "log": out[-1500:]}
    proved = all(res[k] == "proved" for _, k in LEMMAS)
    return {"status": "pass" if proved else "review",
            **({} if proved else {"reason": "the precondition is not proved equivalent to the reference's"}), **res}
