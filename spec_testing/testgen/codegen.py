"""Rust driver codegen.

Synthesizes a `main()` for LeetCode problems: reads one JSON case object
{"input": {param: value}} on stdin, decodes each param, calls Solution::<fn>,
and prints the output value as JSON on stdout. For &mut params it prints
{"ret": <ret>, "<p>_after": <post-state>}.

Serde-free: embeds a small JSON Value parser (reused from post2exe/gen_post2exe.py)
plus generated per-type decode/encode helpers.
"""
from __future__ import annotations

import re

from spec_testing.common.specmodel import SpecModel

# Minimal JSON runtime (Value enum + parser + typed accessors). Self-contained.
RUST_JSON_RUNTIME = r'''
use std::collections::BTreeMap;
use std::io::Read;

#[derive(Clone, Debug)]
enum Value {
    Null,
    Bool(bool),
    Number(String),
    JString(String),
    List(Vec<Value>),
    Object(BTreeMap<String, Value>),
}

impl Value {
    fn as_i128(&self) -> i128 {
        match self {
            Value::Number(s) => s.trim().parse::<i128>().expect("bad integer"),
            Value::Bool(b) => if *b { 1 } else { 0 },
            other => panic!("expected number, got {:?}", other),
        }
    }
    fn as_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Number(s) => s.trim() != "0",
            other => panic!("expected bool, got {:?}", other),
        }
    }
    fn as_list(&self) -> &Vec<Value> {
        match self { Value::List(v) => v, other => panic!("expected list, got {:?}", other) }
    }
    fn as_string(&self) -> String {
        match self {
            Value::JString(s) => s.clone(),
            Value::Number(s) => s.clone(),
            other => panic!("expected string, got {:?}", other),
        }
    }
    fn is_null(&self) -> bool { matches!(self, Value::Null) }
    fn some_inner(&self) -> &Value { self }
}

struct Parser<'a> { s: &'a [u8], pos: usize }

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self { Self { s: input.as_bytes(), pos: 0 } }
    fn parse_root(mut self) -> Value { self.skip_ws(); self.parse_value() }
    fn skip_ws(&mut self) { while self.pos < self.s.len() && self.s[self.pos].is_ascii_whitespace() { self.pos += 1; } }
    fn peek(&self) -> Option<u8> { self.s.get(self.pos).copied() }
    fn bump(&mut self) -> u8 { let ch = self.s[self.pos]; self.pos += 1; ch }
    fn expect(&mut self, e: u8) { self.skip_ws(); let g = self.bump(); assert!(g == e, "expected {:?} got {:?}", e as char, g as char); }
    fn parse_value(&mut self) -> Value {
        self.skip_ws();
        match self.peek() {
            Some(b'"') => Value::JString(self.parse_string()),
            Some(b'[') => Value::List(self.parse_list(b'[', b']')),
            Some(b'(') => Value::List(self.parse_list(b'(', b')')),
            Some(b'{') => Value::Object(self.parse_object()),
            Some(b'-') | Some(b'0'..=b'9') => Value::Number(self.parse_number()),
            Some(b'a'..=b'z') | Some(b'A'..=b'Z') | Some(b'_') => self.parse_ident_value(),
            Some(o) => panic!("bad value start {:?}", o as char),
            None => panic!("unexpected eof"),
        }
    }
    fn parse_string(&mut self) -> String {
        self.expect(b'"'); let mut out = String::new();
        while let Some(ch) = self.peek() {
            self.pos += 1;
            match ch {
                b'\\' => { let e = self.bump(); match e {
                    b'"' => out.push('"'), b'\\' => out.push('\\'), b'/' => out.push('/'),
                    b'n' => out.push('\n'), b'r' => out.push('\r'), b't' => out.push('\t'),
                    _ => out.push(e as char),
                } }
                b'"' => return out,
                _ => out.push(ch as char),
            }
        }
        panic!("unterminated string")
    }
    fn parse_number(&mut self) -> String {
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() || matches!(ch, b'-'|b'+'|b'.'|b'e'|b'E') { self.pos += 1; } else { break; }
        }
        std::str::from_utf8(&self.s[start..self.pos]).unwrap().trim().to_string()
    }
    fn parse_ident(&mut self) -> String {
        let start = self.pos;
        while let Some(ch) = self.peek() { if ch.is_ascii_alphanumeric() || ch == b'_' { self.pos += 1; } else { break; } }
        std::str::from_utf8(&self.s[start..self.pos]).unwrap().to_string()
    }
    fn parse_ident_value(&mut self) -> Value {
        let id = self.parse_ident(); self.skip_ws();
        match id.as_str() {
            "true" => Value::Bool(true),
            "false" => Value::Bool(false),
            "null" | "None" => Value::Null,
            "Some" => { self.expect(b'('); let inner = self.parse_value(); self.skip_ws(); self.expect(b')'); inner }
            other => panic!("bad ident {}", other),
        }
    }
    fn parse_list(&mut self, open: u8, close: u8) -> Vec<Value> {
        self.expect(open); let mut out = Vec::new();
        loop {
            self.skip_ws();
            if self.peek() == Some(close) { self.pos += 1; return out; }
            out.push(self.parse_value()); self.skip_ws();
            match self.peek() {
                Some(b',') => { self.pos += 1; }
                Some(ch) if ch == close => { self.pos += 1; return out; }
                o => panic!("expected , or close, got {:?}", o),
            }
        }
    }
    fn parse_object(&mut self) -> BTreeMap<String, Value> {
        self.expect(b'{'); let mut out = BTreeMap::new();
        loop {
            self.skip_ws();
            if self.peek() == Some(b'}') { self.pos += 1; return out; }
            let key = self.parse_string(); self.skip_ws(); self.expect(b':');
            let v = self.parse_value(); out.insert(key, v); self.skip_ws();
            match self.peek() {
                Some(b',') => { self.pos += 1; }
                Some(b'}') => { self.pos += 1; return out; }
                o => panic!("expected , or }}, got {:?}", o),
            }
        }
    }
}

fn json_escape(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
    out.push('"'); out
}
'''


def _owned_type(rust_type: str) -> str:
    t = rust_type.strip()
    t = re.sub(r"^&\s*mut\s+", "", t)
    t = re.sub(r"^&\s*", "", t)
    return t.strip()


class _TypeHelpers:
    """Accumulates uniquely-named decode/encode helper fns per Rust type."""

    def __init__(self) -> None:
        self.defs: list[str] = []
        self._decode: dict[str, str] = {}
        self._encode: dict[str, str] = {}
        self._n = 0

    def _slug(self, t: str) -> str:
        self._n += 1
        return "t%d" % self._n

    def decode_fn(self, rust_type: str) -> str:
        t = _owned_type(rust_type)
        if t in self._decode:
            return self._decode[t]
        name = "dec_" + self._slug(t)
        self._decode[t] = name  # register before recursion (no cycles expected)
        body = self._decode_body(t, name)
        self.defs.append(body)
        return name

    def _decode_body(self, t: str, name: str) -> str:
        int_types = {"i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128", "usize", "isize"}
        if t in int_types:
            return f"fn {name}(v: &Value) -> {t} {{ v.as_i128() as {t} }}"
        if t == "bool":
            return f"fn {name}(v: &Value) -> bool {{ v.as_bool() }}"
        if t == "char":
            return f"fn {name}(v: &Value) -> char {{ v.as_string().chars().next().expect(\"empty char\") }}"
        if t in ("String", "str"):
            return f"fn {name}(v: &Value) -> String {{ v.as_string() }}"
        m = re.match(r"^Vec\s*<(.+)>$", t)
        if m:
            inner = m.group(1).strip()
            inner_fn = self.decode_fn(inner)
            return (f"fn {name}(v: &Value) -> Vec<{inner}> {{ "
                    f"v.as_list().iter().map(|e| {inner_fn}(e)).collect() }}")
        m = re.match(r"^Option\s*<(.+)>$", t)
        if m:
            inner = m.group(1).strip()
            inner_fn = self.decode_fn(inner)
            return (f"fn {name}(v: &Value) -> Option<{inner}> {{ "
                    f"if v.is_null() {{ None }} else {{ Some({inner_fn}(v.some_inner())) }} }}")
        if t.startswith("(") and t.endswith(")"):
            elems = _split_top(t[1:-1])
            fns = [self.decode_fn(e) for e in elems]
            parts = ", ".join(f"{fn}(&lst[{i}])" for i, fn in enumerate(fns))
            return (f"fn {name}(v: &Value) -> {t} {{ let lst = v.as_list(); ({parts}) }}")
        # Fallback: treat as i128-castable
        return f"fn {name}(v: &Value) -> {t} {{ v.as_i128() as {t} }}"

    def encode_fn(self, rust_type: str) -> str:
        t = _owned_type(rust_type)
        if t in self._encode:
            return self._encode[t]
        name = "enc_" + self._slug(t)
        self._encode[t] = name
        self.defs.append(self._encode_body(t, name))
        return name

    def _encode_body(self, t: str, name: str) -> str:
        int_types = {"i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128", "usize", "isize"}
        if t in int_types:
            return f"fn {name}(x: &{t}) -> String {{ format!(\"{{}}\", x) }}"
        if t == "bool":
            return f"fn {name}(x: &bool) -> String {{ format!(\"{{}}\", x) }}"
        if t == "char":
            return f"fn {name}(x: &char) -> String {{ json_escape(&x.to_string()) }}"
        if t in ("String", "str"):
            return f"fn {name}(x: &String) -> String {{ json_escape(x) }}"
        m = re.match(r"^Vec\s*<(.+)>$", t)
        if m:
            inner = m.group(1).strip()
            inner_fn = self.encode_fn(inner)
            return (f"fn {name}(x: &Vec<{inner}>) -> String {{ "
                    f"let parts: Vec<String> = x.iter().map(|e| {inner_fn}(e)).collect(); "
                    f"format!(\"[{{}}]\", parts.join(\",\")) }}")
        m = re.match(r"^Option\s*<(.+)>$", t)
        if m:
            inner = m.group(1).strip()
            inner_fn = self.encode_fn(inner)
            return (f"fn {name}(x: &Option<{inner}>) -> String {{ "
                    f"match x {{ Some(v) => {inner_fn}(v), None => \"null\".to_string() }} }}")
        if t.startswith("(") and t.endswith(")"):
            elems = _split_top(t[1:-1])
            fns = [self.encode_fn(e) for e in elems]
            parts = ", ".join(f"{fn}(&x.{i})" for i, fn in enumerate(fns))
            joins = " + \",\" + &".join(f"{fn}(&x.{i})" for i, fn in enumerate(fns))
            return (f"fn {name}(x: &{t}) -> String {{ format!(\"[{{}}]\", {joins}) }}")
        return f"fn {name}(x: &{t}) -> String {{ format!(\"{{}}\", x) }}"


def _split_top(inner: str) -> list[str]:
    parts, depth, cur = [], 0, ""
    for ch in inner:
        if ch in "<([":
            depth += 1
        elif ch in ">)]":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur.strip())
    return parts


_JSON_ESCAPE_DEF = r'''
fn json_escape(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
    out.push('"'); out
}
'''


def _enc_arg_expr(rust_type: str, name: str) -> str:
    """How to pass a wrapper param (declared with its exact spec type) to an
    encoder fn that expects `&<owned>`."""
    rt = rust_type.strip()
    if rt.startswith("&mut"):
        return f"&*{name}"
    if rt.startswith("&"):
        return name
    return f"&{name}"


def build_cf_capture_main(main_rs: str, model: SpecModel) -> str:
    """Wrap a Codeforces reference main so every call to `Solution::<fn>` emits a
    `__CAPTURE__{"input":{...},"output":...}` line on stderr carrying the exact
    typed (input, output) the verified function actually received. stdout stays
    the real CF answer. This is ground truth: no heuristic stdin/stdout parsing,
    correct for digit/char representations (cf146A) and multi-output mains where
    only one sub-fn is specified (cf6A)."""
    helpers = _TypeHelpers()
    in_parts: list[str] = []
    for p in model.params:
        efn = helpers.encode_fn(p.rust_type)
        arg = _enc_arg_expr(p.rust_type, p.name)
        in_parts.append(f'"\\"{p.name}\\":".to_string() + &{efn}({arg})')
    ret_enc = helpers.encode_fn(model.ret_type)
    in_expr = (' + &",".to_string() + &'.join(in_parts)) if in_parts else '"".to_string()'
    sig = ", ".join(f"{p.name}: {p.rust_type}" for p in model.params)
    fwd = ", ".join(p.name for p in model.params)

    wrapper = (
        f"fn __cap({sig}) -> {model.ret_type} {{\n"
        f'    let __in = "{{".to_string() + &({in_expr}) + "}}";\n'
        f"    let __r = Solution::{model.fn_name}({fwd});\n"
        f'    eprintln!("__CAPTURE__{{{{\\"input\\":{{}},\\"output\\":{{}}}}}}", __in, {ret_enc}(&__r));\n'
        f"    __r\n"
        f"}}\n"
    )

    # Redirect call sites (never the `impl`-block definition, which is `fn <name>`
    # with no `Solution::` prefix, nor the wrapper appended afterwards).
    patched = re.sub(rf"Solution\s*::\s*{re.escape(model.fn_name)}\b", "__cap", main_rs)

    return "\n".join([
        "#![allow(warnings)]",
        patched,
        _JSON_ESCAPE_DEF,
        "\n".join(helpers.defs),
        wrapper,
    ])


def _ensure_struct(code_rs: str) -> str:
    if re.search(r"\bstruct\s+Solution\b", code_rs):
        return code_rs
    return "pub struct Solution;\n\n" + code_rs


def build_lc_main(code_rs: str, model: SpecModel) -> str:
    """Build a full driver source string for a LeetCode/extended problem."""
    # Drop any existing `fn main` from code.rs (LC code.rs has none, but be safe).
    body = _ensure_struct(code_rs)

    helpers = _TypeHelpers()

    decode_lines: list[str] = []
    call_args: list[str] = []
    mut_after: list[tuple[str, str]] = []  # (param_name, encode_fn)
    for p in model.params:
        dfn = helpers.decode_fn(p.rust_type)
        owned = _owned_type(p.rust_type)
        var = f"arg_{p.name}"
        decode_lines.append(f'    let {"mut " if p.is_mut_ref else ""}{var}: {owned} = {dfn}(get_field(&obj, "{p.name}"));')
        if p.is_mut_ref:
            call_args.append(f"&mut {var}")
            mut_after.append((p.name, helpers.encode_fn(p.rust_type)))
        else:
            call_args.append(var)

    ret_enc = helpers.encode_fn(model.ret_type)
    call = f"Solution::{model.fn_name}({', '.join(call_args)})"

    if mut_after:
        # composite output {"ret":..., "<p>_after":...}
        after_parts = []
        for pname, efn in mut_after:
            after_parts.append(f'"\\"{pname}_after\\":" .to_string() + &{efn}(&arg_{pname})')
        after_join = ' + &",".to_string() + &'.join(after_parts)
        out_expr = (
            f'let __ret = {call};\n'
            f'    let mut __obj = String::from("{{");\n'
            f'    __obj.push_str(&(String::from("\\"ret\\":") + &{ret_enc}(&__ret)));\n'
            f'    __obj.push_str(",");\n'
            f'    __obj.push_str(&({after_join}));\n'
            f'    __obj.push_str("}}");\n'
            f'    println!("{{}}", __obj);'
        )
    else:
        out_expr = (
            f'let __ret = {call};\n'
            f'    println!("{{}}", {ret_enc}(&__ret));'
        )

    get_field = '''
fn get_field<'a>(obj: &'a BTreeMap<String, Value>, key: &str) -> &'a Value {
    if let Some(v) = obj.get(key) { return v; }
    let norm: String = key.chars().filter(|c| c.is_ascii_alphanumeric()).map(|c| c.to_ascii_lowercase()).collect();
    for (k, v) in obj.iter() {
        let kn: String = k.chars().filter(|c| c.is_ascii_alphanumeric()).map(|c| c.to_ascii_lowercase()).collect();
        if kn == norm { return v; }
    }
    panic!("missing field {}", key);
}
'''

    main_fn = f'''
fn main() {{
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    let root = Parser::new(&input).parse_root();
    let obj = match root {{
        Value::Object(o) => {{
            match o.get("input") {{
                Some(Value::Object(inner)) => inner.clone(),
                _ => o,
            }}
        }}
        other => panic!("expected object root, got {{:?}}", other),
    }};
{chr(10).join(decode_lines)}
    {out_expr}
}}
'''

    helper_defs = "\n".join(helpers.defs)
    return "\n".join([
        "#![allow(warnings)]",
        RUST_JSON_RUNTIME,
        get_field,
        body,
        helper_defs,
        main_fn,
    ])
