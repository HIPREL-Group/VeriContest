"""Code tests on the Rust build of a solution.

score.py builds the solution with `dafny build --target:rs` (a library crate,
`solution`) and adds the binary src/bin/harness.rs written by `source(sig)`:

  harness <cases.txt> <out.jsonl> <seconds per case>

Each line of cases.txt is `<case> <tokens of the arguments>` (`case_line`), so
inputs are read at run time rather than compiled in. The harness calls the entry
method on each case in a thread with a 1 GiB stack, times the call alone, and
appends {"case", "status", "time", "output"} to out.jsonl, with status ok,
timeout or runtime_error (a panic) and the result as JSON (a `string` as a JSON
string, a `seq<char>` as a list of characters; several outputs as the testcases'
object, {"nums": .., "return": ..}). A line is flushed per case. A call still
running a second after its limit is recorded as a timeout and the harness exits
with status 3; a crash (a stack overflow) leaves no line for its case. In both
cases score.py restarts the harness after the case.
"""

import re

STACK = 1 << 30
EXIT_TIMEOUT = 3


class IllTyped(Exception):
    pass


def split_top(s):
    """`a, seq<b>, (c, d)` -> [`a`, `seq<b>`, `(c, d)`]."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "<(":
            depth += 1
        elif ch in ">)":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    return out + ([cur.strip()] if cur.strip() else [])


def tuple_types(ty):
    return split_top(ty[1:-1]) if ty.startswith("(") and ty.endswith(")") else None


def seq_elem(ty):
    m = re.fullmatch(r"seq<(.*)>", ty)
    return m.group(1) if m else None


# ----------------------------------------------------------------------------- input

def flat_tuple(v, k):
    """As translator/dafny_driver.py: a k-tuple is a list of k, or nested pairs."""
    if not isinstance(v, list):
        raise IllTyped(f"{v!r} is not a tuple")
    if len(v) == k:
        return v
    if len(v) == 2 and k > 2:
        return [v[0]] + flat_tuple(v[1], k - 1)
    raise IllTyped(f"{v!r} is not a {k}-tuple")


def code_point(c):
    if 0xD800 <= ord(c) <= 0xDFFF:
        raise IllTyped(f"{c!r} is not a Unicode scalar value")
    return str(ord(c))


def tokens(v, ty, out):
    """Append the tokens of JSON value `v` as a Dafny `ty`; the JSON forms are dafny_driver.conv's."""
    if ty in ("int", "nat"):
        if not isinstance(v, int) or isinstance(v, bool) or (ty == "nat" and v < 0):
            raise IllTyped(f"{v!r} is not a {ty}")
        out.append(str(v))
    elif ty == "bool":
        if not isinstance(v, bool):
            raise IllTyped(f"{v!r} is not a bool")
        out.append("1" if v else "0")
    elif ty == "char":
        if not isinstance(v, str) or len(v) != 1:
            raise IllTyped(f"{v!r} is not a char")
        out.append(code_point(v))
    elif ty == "string" or (ty == "seq<char>" and isinstance(v, str)):
        if not isinstance(v, str):
            raise IllTyped(f"{v!r} is not a string")
        out.append(str(len(v)))
        out.extend(code_point(c) for c in v)
    elif seq_elem(ty) is not None:
        if not isinstance(v, list):
            raise IllTyped(f"{v!r} is not a sequence")
        out.append(str(len(v)))
        for x in v:
            tokens(x, seq_elem(ty), out)
    elif tuple_types(ty) is not None:
        ts = tuple_types(ty)
        for x, t in zip(flat_tuple(v, len(ts)), ts):
            tokens(x, t, out)
    else:
        raise IllTyped(f"no conversion for type {ty}")


def case_line(case, sig, inp, norm):
    """One line of cases.txt; parameters are found in `inp` as dafny_driver.args_of finds them."""
    keys = {norm(k): k for k in inp}
    out = [str(case)]
    for vn, _, t in sig["params"]:
        k = vn if vn in inp else keys.get(norm(vn))
        if k is None:
            raise IllTyped(f"no input field for {vn}")
        v, field = inp[k], sig.get("unwrap", {}).get(vn)
        if field and isinstance(v, dict) and field in v:     # a one-field struct as {field: value}
            v = v[field]
        tokens(v, t, out)
    return " ".join(out)


# ----------------------------------------------------------------------------- Rust

def reader(ty, d=0):
    """A Rust expression reading a `ty` from the token iterator `t`."""
    if ty in ("int", "nat"):
        return "rd_int(t)"
    if ty == "bool":
        return "rd_bool(t)"
    if ty == "char":
        return "rd_char(t)"
    if ty in ("string", "seq<char>"):
        return "rd_string(t)"
    if seq_elem(ty) is not None:
        return (f"{{ let n{d} = rd_len(t); let mut v{d} = Vec::with_capacity(n{d}); "
                f"for _ in 0..n{d} {{ v{d}.push({reader(seq_elem(ty), d + 1)}); }} "
                f"Sequence::from_array_owned(v{d}) }}")
    if tuple_types(ty) is not None:
        return "(" + ", ".join(reader(t, d + 1) for t in tuple_types(ty)) + ",)"
    raise IllTyped(f"no conversion for type {ty}")


def writer(ty, x, d=0):
    """Rust statements appending the JSON of `x` (a `&ty`) to the String `o`."""
    if ty in ("int", "nat"):
        return f'o.push_str(&format!("{{:?}}", {x}));'
    if ty == "bool":
        return f'o.push_str(if *{x} {{ "true" }} else {{ "false" }});'
    if ty == "char":
        return f"o.push('\"'); esc(&mut o, {x}.0); o.push('\"');"
    if ty == "string":
        return f"o.push('\"'); for c in {x}.to_array().iter() {{ esc(&mut o, c.0); }} o.push('\"');"
    if seq_elem(ty) is not None:
        return (f"o.push('['); for (i{d}, e{d}) in {x}.to_array().iter().enumerate() {{ "
                f"if i{d} > 0 {{ o.push(','); }} {writer(seq_elem(ty), f'e{d}', d + 1)} }} o.push(']');")
    if tuple_types(ty) is not None:
        parts = [writer(t, f"(&{x}.{i})", d + 1) for i, t in enumerate(tuple_types(ty))]
        return "o.push('['); " + " o.push(','); ".join(parts) + " o.push(']');"
    raise IllTyped(f"no conversion for type {ty}")


def rust_name(name):
    """The Rust backend's name for a Dafny identifier: one with a prime is escaped,
    `count_advancing'` -> `_count__advancing_k`; others are kept."""
    return "_" + name.replace("_", "__").replace("'", "_k") if "'" in name else name


HARNESS = """\
// Generated by eval/rust_harness.py.
use dafny_runtime::{{DafnyChar, DafnyInt, Sequence}};
use std::io::Write;
use std::sync::mpsc;
use std::time::{{Duration, Instant}};

type Toks<'a> = std::str::SplitAsciiWhitespace<'a>;

fn tok<'a>(t: &mut Toks<'a>) -> &'a str {{ t.next().expect("missing token") }}
fn rd_len(t: &mut Toks) -> usize {{ tok(t).parse().unwrap() }}
fn rd_int(t: &mut Toks) -> DafnyInt {{ DafnyInt::parse_bytes(tok(t).as_bytes(), 10) }}
fn rd_bool(t: &mut Toks) -> bool {{ tok(t) == "1" }}
fn rd_char(t: &mut Toks) -> DafnyChar {{ DafnyChar(char::from_u32(tok(t).parse().unwrap()).unwrap()) }}
fn rd_string(t: &mut Toks) -> Sequence<DafnyChar> {{
    let n = rd_len(t);
    Sequence::from_array_owned((0..n).map(|_| rd_char(t)).collect())
}}

fn esc(o: &mut String, c: char) {{
    match c {{
        '"' => o.push_str("\\\\\\""),
        '\\\\' => o.push_str("\\\\\\\\"),
        c if (c as u32) < 0x20 => o.push_str(&format!("\\\\u{{:04x}}", c as u32)),
        c => o.push(c),
    }}
}}

enum Msg {{ Start(usize), Done }}

fn main() {{
    let a: Vec<String> = std::env::args().collect();
    let (cases, out_path, limit) = (a[1].clone(), a[2].clone(), a[3].parse::<f64>().unwrap());
    let (tx, rx) = mpsc::channel();
    let path = out_path.clone();
    let worker = std::thread::Builder::new().stack_size({stack}).spawn(move || {{
        let text = std::fs::read_to_string(&cases).unwrap();
        let mut out = std::fs::OpenOptions::new().create(true).append(true).open(&path).unwrap();
        for line in text.lines() {{
            let t = &mut line.split_ascii_whitespace();
            let case: usize = tok(t).parse().unwrap();
{reads}
            tx.send(Msg::Start(case)).unwrap();
            let t0 = Instant::now();
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {call}));
            let secs = t0.elapsed().as_secs_f64();
            let rec = match r {{
                Ok(y) if secs <= limit => {{
                    let mut o = String::new();
                    {write}
                    format!("{{{{\\"case\\": {{}}, \\"status\\": \\"ok\\", \\"time\\": {{:.4}}, \\"output\\": {{}}}}}}", case, secs, o)
                }}
                Ok(_) => format!("{{{{\\"case\\": {{}}, \\"status\\": \\"timeout\\", \\"time\\": {{:.4}}}}}}", case, secs),
                Err(_) => format!("{{{{\\"case\\": {{}}, \\"status\\": \\"runtime_error\\", \\"detail\\": \\"panic\\"}}}}", case),
            }};
            writeln!(out, "{{}}", rec).unwrap();
            out.flush().unwrap();
            tx.send(Msg::Done).unwrap();
        }}
    }}).unwrap();
    let grace = Duration::from_secs_f64(limit + 1.0);
    while let Ok(msg) = rx.recv() {{
        if let Msg::Start(case) = msg {{
            if let Err(mpsc::RecvTimeoutError::Timeout) = rx.recv_timeout(grace) {{
                let mut out = std::fs::OpenOptions::new().create(true).append(true).open(&out_path).unwrap();
                writeln!(out, "{{{{\\"case\\": {{}}, \\"status\\": \\"timeout\\", \\"time\\": {{:.4}}}}}}", case, limit).unwrap();
                std::process::exit({exit_timeout});
            }}
        }}
    }}
    std::process::exit(if worker.join().is_ok() {{ 0 }} else {{ 2 }});
}}
"""


def source(sig):
    """src/bin/harness.rs for the entry method `sig` (score.reference_sig)."""
    reads = "\n".join(f"            let a{i} = {reader(t)};" for i, (_, _, t) in enumerate(sig["params"]))
    args = ", ".join(f"a{i}" if t == "bool" else f"&a{i}" for i, (_, _, t) in enumerate(sig["params"]))
    call = f"solution::_module::_default::{rust_name(sig['name'])}({args})"
    if sig.get("outs"):
        # several outputs (a Rust tuple) as the testcases give them: {"nums": .., "return": ..}
        write = "o.push('{'); " + " o.push(','); ".join(
            f'o.push_str("\\"{k}\\": "); ' + writer(t, f"(&y.{i})") for i, (k, _, t) in enumerate(sig["outs"])) \
            + " o.push('}');"
    else:
        write = writer(sig["ret"][1], "(&y)")
    return HARNESS.format(stack=STACK, reads=reads, call=call, write=write, exit_timeout=EXIT_TIMEOUT)
