#!/usr/bin/env python3
"""
Generate per-problem stdin/stdout harness that wraps code.rs as an oracle.

For each problem, produces a self-contained Rust file (harness.rs) that:
  1. Reads one JSON object per line from stdin
  2. Parses each field into the function's input types
  3. Calls Solution::method(args...)
  4. Prints one JSON object per line: {"input": {field1: ..., field2: ...}, "output": result}
     (same top-level shape as tests/testcases.jsonl from gen.rs)

**Codeforces (target):** ``tests/testcases.jsonl`` uses string ``input`` and string ``output``
(full stdin/stdout text for ``main.rs``). Harnesses that call ``main.rs`` via
``tests/cf_main_bin`` were emitted by a one-off migration and are checked into the
corpus; they must not be overwritten by this script's default ``render_harness`` output.

Usage
-----
    python test_gen/build_harness.py --all
    python test_gen/build_harness.py --kind leetcode
    python test_gen/build_harness.py --problem benchmark/leetcode/lc1
    python test_gen/build_harness.py --all --compile  # also compile with rustc
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BENCH_ROOT = REPO_ROOT / "benchmark"

# JSON stdin/stdout oracle that uses ``include!("../code.rs")`` (see ``build_reference_oracle_bin``).
REFERENCE_ORACLE_RS_NAME = "reference_oracle.rs"
REFERENCE_ORACLE_BIN_NAME = "reference_oracle_bin"


def compile_cf_main_bin(problem_dir: Path, *, compile_timeout: int = 120) -> str:
    """Compile ``main.rs`` to ``tests/cf_main_bin`` (for CF stdin harnesses). Empty = ok."""
    main_rs = problem_dir / "main.rs"
    tests_dir = problem_dir / "tests"
    if not main_rs.is_file():
        return ""
    cf_bin = tests_dir / "cf_main_bin"
    result = subprocess.run(
        ["rustc", "--edition", "2021", "-O", str(main_rs), "-o", str(cf_bin)],
        cwd=str(problem_dir),
        capture_output=True,
        text=True,
        timeout=compile_timeout,
    )
    if result.returncode != 0:
        return (result.stderr or result.stdout or "rustc main.rs failed")[:4000]
    return ""


@dataclass
class StructField:
    name: str
    rust_type: str

@dataclass
class StructInfo:
    name: str
    fields: list[StructField]

@dataclass
class Signature:
    method: str
    args: list[tuple[str, str]]
    ret: str
    owner: str = "Solution"  # which impl block owns this method


def _find_balanced_parens(text: str, start: int) -> int | None:
    if start >= len(text) or text[start] != '(':
        return None
    depth = 0
    for i in range(start, len(text)):
        if text[i] == '(':
            depth += 1
        elif text[i] == ')':
            depth -= 1
            if depth == 0:
                return i + 1
    return None


def extract_structs(code_rs: str) -> dict[str, StructInfo]:
    """Extract pub struct definitions and their pub fields from code.rs."""
    structs: dict[str, StructInfo] = {}
    for m in re.finditer(r'pub\s+struct\s+(\w+)\s*\{', code_rs):
        name = m.group(1)
        brace_start = m.end() - 1
        depth = 0
        brace_end = brace_start
        for i in range(brace_start, len(code_rs)):
            if code_rs[i] == '{':
                depth += 1
            elif code_rs[i] == '}':
                depth -= 1
                if depth == 0:
                    brace_end = i
                    break
        body = code_rs[brace_start + 1:brace_end]
        fields = []
        for fm in re.finditer(r'pub\s+(\w+)\s*:\s*([^,}]+)', body):
            fields.append(StructField(fm.group(1).strip(), fm.group(2).strip()))
        if fields:
            structs[name] = StructInfo(name, fields)
    return structs


def find_method_owner(code_rs: str, fn_name: str) -> str:
    """Find which impl block owns a function. Returns struct name or 'Solution'."""
    for m in re.finditer(r'impl\s+(\w+)\s*\{', code_rs):
        struct_name = m.group(1)
        brace_start = m.end() - 1
        depth = 0
        brace_end = brace_start
        for i in range(brace_start, len(code_rs)):
            if code_rs[i] == '{':
                depth += 1
            elif code_rs[i] == '}':
                depth -= 1
                if depth == 0:
                    brace_end = i
                    break
        impl_body = code_rs[brace_start:brace_end + 1]
        if re.search(rf'fn\s+{re.escape(fn_name)}\s*\(', impl_body):
            return struct_name
    return "Solution"


def parse_signature(code_rs: str, target_name: str | None = None) -> Signature:
    if target_name:
        pattern = rf'(?:pub\s+)?fn\s+({re.escape(target_name)})\s*\('
    else:
        pattern = r'(?:pub\s+)?fn\s+(\w+)\s*\('
    m = re.search(pattern, code_rs, re.DOTALL)
    if not m:
        raise ValueError(f"no `fn {target_name or ''}` signature found in code.rs")
    name = m.group(1)
    paren_start = m.end() - 1
    paren_end = _find_balanced_parens(code_rs, paren_start)
    if paren_end is None:
        raise ValueError("unbalanced parentheses in signature")
    args_raw = code_rs[paren_start + 1: paren_end - 1].strip()

    rest = code_rs[paren_end:]
    rm = re.match(r'\s*(->\s*(?P<ret>.+?))?\s*\{', rest, re.DOTALL)
    ret = (rm.group("ret") or "()").strip() if rm else "()"

    args: list[tuple[str, str]] = []
    if args_raw:
        depth_angle = depth_paren = 0
        cur = ""
        parts: list[str] = []
        for ch in args_raw:
            if ch == "<":
                depth_angle += 1
            elif ch == ">":
                depth_angle -= 1
            elif ch == "(":
                depth_paren += 1
            elif ch == ")":
                depth_paren -= 1
            if ch == "," and depth_angle == 0 and depth_paren == 0:
                parts.append(cur)
                cur = ""
            else:
                cur += ch
        if cur.strip():
            parts.append(cur)
        for p in parts:
            p = p.strip()
            if p in ("&self", "&mut self", "self"):
                continue
            if ":" not in p:
                raise ValueError(f"cannot parse arg fragment: {p!r}")
            n, t = p.split(":", 1)
            n = n.strip()
            if n.startswith("mut "):
                n = n[4:]
            args.append((n.strip(), t.strip()))
    owner = find_method_owner(code_rs, name)
    return Signature(method=name, args=args, ret=ret, owner=owner)


# ---------------------------------------------------------------------------
# Type classification helpers
# ---------------------------------------------------------------------------

def strip_ref(t: str) -> tuple[str, bool]:
    """Strip leading & or &mut, return (inner_type, is_ref)."""
    t = t.strip()
    if t.startswith("&mut "):
        return t[5:].strip(), True
    if t.startswith("&"):
        return t[1:].strip(), True
    return t, False


def is_vec_type(t: str) -> tuple[bool, str]:
    """Check if type is Vec<T>, return (True, T) or (False, '')."""
    t = t.strip()
    if t.startswith("Vec<") and t.endswith(">"):
        return True, t[4:-1].strip()
    return False, ""


def is_tuple_type(t: str) -> tuple[bool, list[str]]:
    """Check if type is (T1, T2, ...), return (True, [T1, T2, ...])."""
    t = t.strip()
    if t.startswith("(") and t.endswith(")"):
        inner = t[1:-1].strip()
        if not inner:
            return True, []
        parts = []
        depth_a = depth_p = 0
        cur = ""
        for ch in inner:
            if ch == "<":
                depth_a += 1
            elif ch == ">":
                depth_a -= 1
            elif ch == "(":
                depth_p += 1
            elif ch == ")":
                depth_p -= 1
            if ch == "," and depth_a == 0 and depth_p == 0:
                parts.append(cur.strip())
                cur = ""
            else:
                cur += ch
        if cur.strip():
            parts.append(cur.strip())
        return True, parts
    return False, []


def is_option_type(t: str) -> tuple[bool, str]:
    t = t.strip()
    if t.startswith("Option<") and t.endswith(">"):
        return True, t[7:-1].strip()
    return False, ""


# ---------------------------------------------------------------------------
# JSON parsing code generation (Rust)
# ---------------------------------------------------------------------------

def gen_parse_expr(var_name: str, json_expr: str, rust_type: str) -> list[str]:
    """Generate Rust lines to parse `json_expr` (a &str of JSON) into `rust_type`."""
    inner, is_ref = strip_ref(rust_type)
    needs_mut = rust_type.strip().startswith("&mut ")
    if is_ref:
        lines = gen_parse_expr(var_name, json_expr, inner)
        if needs_mut:
            lines = [l.replace(f'let {var_name}:', f'let mut {var_name}:') for l in lines]
        return lines

    is_vec, elem_type = is_vec_type(inner)
    is_tup, tup_elems = is_tuple_type(inner)
    is_opt, opt_inner = is_option_type(inner)

    if inner == "String":
        return [f'let {var_name}: String = parse_string({json_expr});']
    elif inner in ("i32", "i64", "i128", "u32", "u64", "u128", "usize", "isize", "u8"):
        return [f'let {var_name}: {inner} = parse_number::<{inner}>({json_expr});']
    elif inner == "bool":
        return [f'let {var_name}: bool = parse_bool({json_expr});']
    elif is_vec:
        is_inner_vec, inner_inner = is_vec_type(elem_type)
        is_inner_tup, tup_inner_elems = is_tuple_type(elem_type)
        if elem_type in ("i32", "i64", "i128", "u32", "u64", "u128", "usize", "isize", "u8"):
            return [f'let {var_name}: Vec<{elem_type}> = parse_num_array::<{elem_type}>({json_expr});']
        elif elem_type == "bool":
            return [f'let {var_name}: Vec<bool> = parse_bool_array({json_expr});']
        elif elem_type == "String":
            return [f'let {var_name}: Vec<String> = parse_string_array({json_expr});']
        elif is_inner_vec:
            if inner_inner in ("i32", "i64", "i128", "u32", "u64", "u128", "usize", "isize", "u8"):
                return [f'let {var_name}: Vec<Vec<{inner_inner}>> = parse_2d_num_array::<{inner_inner}>({json_expr});']
            elif inner_inner == "bool":
                return [f'let {var_name}: Vec<Vec<bool>> = parse_2d_bool_array({json_expr});']
            elif inner_inner == "String":
                return [f'let {var_name}: Vec<Vec<String>> = parse_2d_string_array({json_expr});']
            else:
                return [f'let {var_name}: Vec<Vec<{inner_inner}>> = todo!("parse Vec<Vec<{inner_inner}>>"); // MANUAL REVIEW']
        elif is_inner_tup and len(tup_inner_elems) == 2:
            return [f'let {var_name}: Vec<({tup_inner_elems[0]}, {tup_inner_elems[1]})> = parse_tuple2_array::<{tup_inner_elems[0]}, {tup_inner_elems[1]}>({json_expr});']
        elif elem_type == "char":
            return [f'let {var_name}: Vec<char> = parse_char_vec({json_expr});']
        else:
            return [f'let {var_name}: Vec<{elem_type}> = todo!("parse Vec<{elem_type}>"); // MANUAL REVIEW']
    elif is_tup and len(tup_elems) == 2:
        return [f'let {var_name}: ({tup_elems[0]}, {tup_elems[1]}) = parse_tuple2::<{tup_elems[0]}, {tup_elems[1]}>({json_expr});']
    elif is_opt:
        return [f'let {var_name}: Option<{opt_inner}> = parse_option({json_expr}); // MANUAL REVIEW']
    else:
        return [f'let {var_name}: {inner} = todo!("parse {inner}"); // MANUAL REVIEW']


def gen_output_expr(expr: str, rust_type: str) -> str:
    """Generate Rust expression to serialize a value of `rust_type` to JSON string."""
    inner, is_ref = strip_ref(rust_type)
    is_vec, elem_type = is_vec_type(inner)
    is_tup, tup_elems = is_tuple_type(inner)
    is_opt, opt_inner = is_option_type(inner)

    # Option<T> as JSON: null or the T fragment (avoids `{:?}` / invalid JSON in stdout).
    if is_opt:
        v = "v"
        arm_inner = gen_output_expr(v, opt_inner)
        base_t, _ = strip_ref(opt_inner)
        if base_t in (
            "i32", "i64", "i128", "u32", "u64", "u128", "usize", "isize", "u8", "f32", "f64",
        ):
            arm = f"format!(\"{{}}\", {v})"
        elif base_t == "bool":
            arm = f"String::from(if {v} {{ \"true\" }} else {{ \"false\" }})"
        else:
            arm = arm_inner
        return f"match {expr} {{ None => String::from(\"null\"), Some({v}) => {arm} }}"

    if inner in ("i32", "i64", "i128", "u32", "u64", "u128", "usize", "isize", "u8"):
        return f'{expr}'
    elif inner == "bool":
        return f'if {expr} {{ "true" }} else {{ "false" }}'
    elif inner == "String":
        return f'format_json_string(&{expr})'
    elif is_vec:
        is_inner_vec, inner_inner = is_vec_type(elem_type)
        is_inner_tup, tup_inner_elems = is_tuple_type(elem_type)
        if elem_type in ("i32", "i64", "i128", "u32", "u64", "u128", "usize", "isize", "u8"):
            return f'format_num_array(&{expr})'
        elif elem_type == "bool":
            return f'format_bool_array(&{expr})'
        elif elem_type == "String":
            return f'format_string_array(&{expr})'
        elif is_inner_vec:
            if inner_inner == "bool":
                return f'format_2d_bool_array(&{expr})'
            else:
                return f'format_2d_num_array(&{expr})'
        elif is_inner_tup and len(tup_inner_elems) == 2:
            t0, t1 = tup_inner_elems[0], tup_inner_elems[1]
            num_ty = {
                "i32", "i64", "i128", "u32", "u64", "u128", "usize", "isize", "u8",
            }
            if t0 in num_ty and t1 in num_ty:
                return f'format_tuple2_array_json(&{expr})'
        elif elem_type == "char":
            return f'format_char_vec(&{expr})'
        else:
            return f'format!("{{:?}}", {expr}) /* MANUAL REVIEW */'
    elif is_tup and len(tup_elems) >= 2:
        part_exprs = [gen_output_expr(f"{expr}.{i}", tup_elems[i]) for i in range(len(tup_elems))]
        inner = ",".join(["{}" for _ in tup_elems])
        return f'format!("[{inner}]", {", ".join(part_exprs)})'
    elif inner == "()":
        return '"null"'
    else:
        return f'format!("{{:?}}", {expr}) /* MANUAL REVIEW */'


# ---------------------------------------------------------------------------
# Harness Rust source generation
# ---------------------------------------------------------------------------

HARNESS_PRELUDE = r'''
use std::io::{self, BufRead, Write, BufWriter};

trait StrExt {
    fn unicode_len(&self) -> usize;
    fn get_char(&self, i: usize) -> char;
}
impl StrExt for str {
    fn unicode_len(&self) -> usize { self.chars().count() }
    fn get_char(&self, i: usize) -> char { self.chars().nth(i).unwrap() }
}

trait VecExt<T> {
    fn set(&mut self, i: usize, val: T);
}
impl<T> VecExt<T> for Vec<T> {
    fn set(&mut self, i: usize, val: T) { self[i] = val; }
}

fn find_key<'a>(line: &'a str, key: &str) -> &'a str {
    let pat = format!("\"{}\"", key);
    let start = line.find(&pat).expect(&format!("key '{}' not found", key));
    let after_key = &line[start + pat.len()..];
    let colon = after_key.find(':').expect("no colon after key") + 1;
    let rest = after_key[colon..].trim_start();
    rest
}

fn extract_value<'a>(s: &'a str) -> &'a str {
    let s = s.trim_start();
    if s.starts_with('"') {
        let end = s[1..].find('"').expect("unterminated string") + 2;
        let after = s[end..].trim_start();
        if after.starts_with(',') || after.starts_with('}') || after.is_empty() {
            return &s[..end];
        }
        &s[..end]
    } else if s.starts_with('[') {
        let mut depth = 0;
        for (i, c) in s.char_indices() {
            match c {
                '[' => depth += 1,
                ']' => { depth -= 1; if depth == 0 { return &s[..i+1]; } }
                _ => {}
            }
        }
        s
    } else if s.starts_with('{') {
        let mut depth = 0;
        for (i, c) in s.char_indices() {
            match c {
                '{' => depth += 1,
                '}' => { depth -= 1; if depth == 0 { return &s[..i+1]; } }
                _ => {}
            }
        }
        s
    } else {
        let end = s.find(|c: char| c == ',' || c == '}' || c == ']').unwrap_or(s.len());
        s[..end].trim_end()
    }
}

fn get_field<'a>(line: &'a str, key: &str) -> &'a str {
    let rest = find_key(line, key);
    extract_value(rest)
}

trait ParseNum: Sized {
    fn parse_from(s: &str) -> Self;
}
macro_rules! impl_parse_num {
    ($($t:ty),*) => { $(
        impl ParseNum for $t {
            fn parse_from(s: &str) -> Self { s.trim().parse().expect(&format!("bad number: {}", s)) }
        }
    )* }
}
impl_parse_num!(i32, i64, i128, u32, u64, u128, usize, isize, u8);

fn parse_number<T: ParseNum>(s: &str) -> T {
    let s = s.trim();
    if s == "null" || s == "true" {
        T::parse_from("1")
    } else if s == "false" {
        T::parse_from("0")
    } else {
        T::parse_from(s)
    }
}

fn parse_bool(s: &str) -> bool {
    let s = s.trim();
    s == "true" || s == "1"
}

fn parse_string(s: &str) -> String {
    let s = s.trim();
    if s.starts_with('"') && s.ends_with('"') {
        s[1..s.len()-1].to_string()
    } else {
        s.to_string()
    }
}

fn parse_char_vec(s: &str) -> Vec<char> {
    parse_string(s).chars().collect()
}

fn parse_num_array<T: ParseNum>(s: &str) -> Vec<T> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let inner = &s[1..s.len()-1];
    inner.split(',').map(|x| T::parse_from(x.trim())).collect()
}

fn parse_bool_array(s: &str) -> Vec<bool> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let inner = &s[1..s.len()-1];
    inner.split(',').map(|x| parse_bool(x.trim())).collect()
}

fn parse_string_array(s: &str) -> Vec<String> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let mut result = Vec::new();
    let inner = &s[1..s.len()-1];
    let mut in_str = false;
    let mut cur = String::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '"' {
            if in_str {
                result.push(cur.clone());
                cur.clear();
                in_str = false;
            } else {
                in_str = true;
            }
        } else if in_str {
            cur.push(c);
        }
    }
    result
}

fn parse_2d_num_array<T: ParseNum>(s: &str) -> Vec<Vec<T>> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let mut result = Vec::new();
    let inner = &s[1..s.len()-1];
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '[' => { if depth == 0 { start = i; } depth += 1; }
            ']' => { depth -= 1; if depth == 0 { result.push(parse_num_array(&inner[start..i+1])); } }
            _ => {}
        }
    }
    result
}

fn parse_2d_bool_array(s: &str) -> Vec<Vec<bool>> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let mut result = Vec::new();
    let inner = &s[1..s.len()-1];
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '[' => { if depth == 0 { start = i; } depth += 1; }
            ']' => { depth -= 1; if depth == 0 { result.push(parse_bool_array(&inner[start..i+1])); } }
            _ => {}
        }
    }
    result
}

fn parse_2d_string_array(s: &str) -> Vec<Vec<String>> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let mut result = Vec::new();
    let inner = &s[1..s.len()-1];
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '[' => { if depth == 0 { start = i; } depth += 1; }
            ']' => { depth -= 1; if depth == 0 { result.push(parse_string_array(&inner[start..i+1])); } }
            _ => {}
        }
    }
    result
}

fn parse_tuple2<A: ParseNum, B: ParseNum>(s: &str) -> (A, B) {
    let s = s.trim();
    let inner = &s[1..s.len()-1];
    let parts: Vec<&str> = inner.splitn(2, ',').collect();
    (A::parse_from(parts[0].trim()), B::parse_from(parts[1].trim()))
}

fn parse_tuple2_array<A: ParseNum, B: ParseNum>(s: &str) -> Vec<(A, B)> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let mut result = Vec::new();
    let inner = &s[1..s.len()-1];
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '[' => { if depth == 0 { start = i; } depth += 1; }
            ']' => { depth -= 1; if depth == 0 { result.push(parse_tuple2(&inner[start..i+1])); } }
            _ => {}
        }
    }
    result
}

fn format_json_string(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

fn format_num_array<T: std::fmt::Display>(v: &[T]) -> String {
    let parts: Vec<String> = v.iter().map(|x| x.to_string()).collect();
    format!("[{}]", parts.join(","))
}

fn format_bool_array(v: &[bool]) -> String {
    let parts: Vec<&str> = v.iter().map(|b| if *b { "true" } else { "false" }).collect();
    format!("[{}]", parts.join(","))
}

fn format_string_array(v: &[String]) -> String {
    let parts: Vec<String> = v.iter().map(|s| format_json_string(s)).collect();
    format!("[{}]", parts.join(","))
}

fn format_char_vec(v: &[char]) -> String {
    format_json_string(&v.iter().collect::<String>())
}

fn format_2d_num_array<T: std::fmt::Display>(v: &[Vec<T>]) -> String {
    let parts: Vec<String> = v.iter().map(|row| format_num_array(row)).collect();
    format!("[{}]", parts.join(","))
}

fn format_2d_bool_array(v: &[Vec<bool>]) -> String {
    let parts: Vec<String> = v.iter().map(|row| format_bool_array(row)).collect();
    format!("[{}]", parts.join(","))
}

fn format_tuple2_array_json<T: std::fmt::Display, U: std::fmt::Display>(v: &[(T, U)]) -> String {
    let parts: Vec<String> = v.iter().map(|(a, b)| format!("[{},{}]", a, b)).collect();
    format!("[{}]", parts.join(","))
}
'''


def _has_new_constructor(code_rs_text: str, struct_name: str) -> Signature | None:
    """Check if struct has a `fn new(...)` constructor, return its signature."""
    for m in re.finditer(rf'impl\s+{re.escape(struct_name)}\s*\{{', code_rs_text):
        brace_start = m.end() - 1
        depth = 0
        brace_end = brace_start
        for i in range(brace_start, len(code_rs_text)):
            if code_rs_text[i] == '{':
                depth += 1
            elif code_rs_text[i] == '}':
                depth -= 1
                if depth == 0:
                    brace_end = i
                    break
        impl_body = code_rs_text[brace_start:brace_end + 1]
        if re.search(r'fn\s+new\s*\(', impl_body):
            try:
                return parse_signature(impl_body, "new")
            except Exception:
                pass
    return None


def _resolve_struct_type(arg_type: str) -> str | None:
    """If arg_type refers to a custom struct (possibly by reference), return the name."""
    inner, _ = strip_ref(arg_type)
    if inner and inner[0].isupper() and inner not in ("Vec", "String", "Option"):
        return inner
    return None


def render_harness(code_rs_text: str, sig: Signature,
                   structs: dict[str, StructInfo] | None = None,
                   *,
                   embed_code: bool = True) -> str:
    """Generate the complete harness.rs source.

    If ``embed_code`` is True (default), inlines ``code.rs`` text. If False, emits
    ``include!(\"../code.rs\");`` so the oracle reads the problem's ``code.rs`` from
    disk (paths are relative to the generated file under ``tests/``).
    """
    if structs is None:
        structs = extract_structs(code_rs_text)
    lines: list[str] = []

    has_impl = "impl Solution" in code_rs_text
    already_defines_solution = bool(re.search(r'pub\s+struct\s+Solution\b', code_rs_text))
    if has_impl and not already_defines_solution:
        lines.append("pub struct Solution;\n")
    if embed_code:
        lines.append(code_rs_text.strip())
    else:
        lines.append('include!("../code.rs");\n')
    lines.append("")
    lines.append(HARNESS_PRELUDE.strip())
    lines.append("")

    is_self_method = sig.owner != "Solution" and sig.owner in structs
    owner_struct = structs.get(sig.owner) if is_self_method else None
    owner_new_sig = _has_new_constructor(code_rs_text, sig.owner) if is_self_method else None

    # Collect all JSON fields: the method's own args + any struct construction fields
    # For self-methods, the struct's construction args come from JSON too.
    # `json_fields` tracks (json_key, var_name, rust_type) for serialization.
    json_fields: list[tuple[str, str, str]] = []

    lines.append("fn main() {")
    lines.append("    let stdin = io::stdin();")
    lines.append("    let stdout = io::stdout();")
    lines.append("    let mut out = BufWriter::new(stdout.lock());")
    lines.append("    for line in stdin.lock().lines() {")
    lines.append('        let line = line.expect("read line");')
    lines.append("        let line = line.trim();")
    lines.append('        if line.is_empty() || !line.starts_with(\'{\') { continue; }')

    # If this is a self-method on a custom struct, parse constructor args from JSON.
    # Defer actual struct construction until after serialization.
    owner_construction: str | None = None
    if is_self_method:
        if owner_new_sig:
            for arg_name, arg_type in owner_new_sig.args:
                parse_lines = gen_parse_expr(arg_name, f'get_field(line, "{arg_name}")', arg_type)
                for pl in parse_lines:
                    lines.append(f"        {pl}")
                json_fields.append((arg_name, arg_name, arg_type))
            ctor_args = ", ".join(n for n, _ in owner_new_sig.args)
            owner_construction = f"        let _instance = {sig.owner}::new({ctor_args});"
        elif owner_struct:
            for sf in owner_struct.fields:
                parse_lines = gen_parse_expr(sf.name, f'get_field(line, "{sf.name}")', sf.rust_type)
                for pl in parse_lines:
                    lines.append(f"        {pl}")
                json_fields.append((sf.name, sf.name, sf.rust_type))
            field_inits = ", ".join(f"{sf.name}" for sf in owner_struct.fields)
            owner_construction = f"        let _instance = {sig.owner} {{ {field_inits} }};"

    # Parse each method argument and track struct construction that must happen
    # after serialization (to avoid use-after-move).
    struct_constructions: list[str] = []  # deferred struct construction lines
    for arg_name, arg_type in sig.args:
        struct_type = _resolve_struct_type(arg_type)
        if struct_type and struct_type in structs:
            si = structs[struct_type]
            for sf in si.fields:
                field_var = f"_struct_{arg_name}_{sf.name}"
                parse_lines = gen_parse_expr(field_var, f'get_field(line, "{sf.name}")', sf.rust_type)
                for pl in parse_lines:
                    lines.append(f"        {pl}")
                json_fields.append((sf.name, field_var, sf.rust_type))
            field_inits = ", ".join(f"{sf.name}: _struct_{arg_name}_{sf.name}" for sf in si.fields)
            struct_constructions.append(
                f"        let {arg_name} = {struct_type} {{ {field_inits} }};")
        else:
            parse_lines = gen_parse_expr(arg_name, f'get_field(line, "{arg_name}")', arg_type)
            for pl in parse_lines:
                lines.append(f"        {pl}")
            json_fields.append((arg_name, arg_name, arg_type))

    # Serialize input fields BEFORE struct construction (to avoid use-after-move)
    for i, (json_key, var_name, arg_type) in enumerate(json_fields):
        inner_type, _ = strip_ref(arg_type)
        ser = gen_output_expr(var_name, inner_type)
        lines.append(f'        let _f{i} = format!("\\"{json_key}\\\": {{}}", {ser});')

    # Now construct structs (after serialization to avoid use-after-move)
    if owner_construction:
        lines.append(owner_construction)
    for sc_line in struct_constructions:
        lines.append(sc_line)

    # Call function
    call_arg_parts = []
    for arg_name, arg_type in sig.args:
        t = arg_type.strip()
        if t.startswith("&mut "):
            call_arg_parts.append(f"&mut {arg_name}")
        elif t.startswith("&"):
            call_arg_parts.append(f"&{arg_name}")
        else:
            call_arg_parts.append(arg_name)
    call_args = ", ".join(call_arg_parts)

    if is_self_method:
        call_expr = f"_instance.{sig.method}({call_args})"
    elif has_impl and sig.owner == "Solution":
        call_expr = f"Solution::{sig.method}({call_args})"
    else:
        call_expr = f"{sig.method}({call_args})"

    if sig.ret == "()":
        lines.append(f"        {call_expr};")
        output_str = 'String::from("\\\"output\\\": null")'
    else:
        lines.append(f"        let result = {call_expr};")
        output_fmt = gen_output_expr("result", sig.ret)
        output_str = f'format!("\\\"output\\\": {{}}", {output_fmt})'

    lines.append(f"        let _out = {output_str};")

    n_in = len(json_fields)
    input_refs = [f"_f{i}" for i in range(n_in)]
    if input_refs:
        lines.append(f"        let parts = [{', '.join(input_refs)}];")
        lines.append('        write!(out, "{{\\"input\\": {{").unwrap();')
        lines.append("        for (i, part) in parts.iter().enumerate() {")
        lines.append("            if i > 0 { write!(out, \", \").unwrap(); }")
        lines.append('            write!(out, "{}", part).unwrap();')
        lines.append("        }")
        lines.append('        writeln!(out, "}}, {}}}", _out).unwrap();')
    else:
        lines.append('        writeln!(out, "{{\\"input\\": {{}}, {}}}", _out).unwrap();')

    lines.append("    }")
    lines.append("}")

    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Problem iteration
# ---------------------------------------------------------------------------

def load_ignore_set(kind_root: Path) -> set[str]:
    ignore_file = kind_root / ".benchmark-ignore"
    if not ignore_file.exists():
        return set()
    return {line.strip() for line in ignore_file.read_text().splitlines() if line.strip()}


def iter_problems(kind: str) -> list[Path]:
    kinds: list[Path] = []
    if kind in ("leetcode", "both"):
        kinds.append(BENCH_ROOT / "leetcode")
    if kind in ("codeforces", "both"):
        kinds.append(BENCH_ROOT / "codeforces")
    out: list[Path] = []
    for root in kinds:
        if not root.exists():
            continue
        ignore = load_ignore_set(root)
        for p in sorted(root.iterdir()):
            if not p.is_dir():
                continue
            if p.name in ignore:
                continue
            if (p / "code.rs").exists():
                out.append(p)
    return out


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

@dataclass
class Result:
    problem: Path
    status: str
    detail: str = ""


def find_main_fn_name(problem_dir: Path) -> str | None:
    """Find the main function name from spec.rs (the one with requires/ensures)."""
    spec_rs = problem_dir / "spec.rs"
    if not spec_rs.exists():
        return None
    text = spec_rs.read_text()
    # Find the fn that has `requires` or `ensures` after it
    # Pattern: pub fn NAME(...) -> ... requires/ensures
    matches = list(re.finditer(r'(?:pub\s+)?fn\s+(\w+)\s*\(', text))
    for m in reversed(matches):
        after = text[m.end():]
        # Check if this fn has requires or ensures nearby
        # Find the matching closing paren, then look for requires/ensures
        paren_start = m.end() - 1
        paren_end = _find_balanced_parens(text, paren_start)
        if paren_end is None:
            continue
        rest = text[paren_end:paren_end + 500]
        if 'requires' in rest or 'ensures' in rest:
            return m.group(1)
    # Fallback: return the last fn name
    if matches:
        return matches[-1].group(1)
    return None


def build_one(problem_dir: Path, do_compile: bool) -> Result:
    code_rs = problem_dir / "code.rs"
    if not code_rs.exists():
        return Result(problem_dir, "skipped_no_code")

    target_name = find_main_fn_name(problem_dir)
    try:
        sig = parse_signature(code_rs.read_text(), target_name)
    except Exception as e:
        return Result(problem_dir, "error", f"parse_signature: {e}")

    tests_dir = problem_dir / "tests"
    tests_dir.mkdir(parents=True, exist_ok=True)

    harness_rs = tests_dir / "harness.rs"
    if harness_rs.exists():
        htxt = harness_rs.read_text()
        if (
            "extract_input_stdin" in htxt
            or "run_cf_main_stdin" in htxt
            or "extract_cf_io_input" in htxt
        ):
            if do_compile:
                err = compile_cf_main_bin(problem_dir)
                if err:
                    return Result(problem_dir, "compile_error", err)
                harness_bin = tests_dir / "harness_bin"
                result = subprocess.run(
                    ["rustc", str(harness_rs), "-o", str(harness_bin), "-O"],
                    capture_output=True, text=True, timeout=120,
                )
                if result.returncode != 0:
                    e = (result.stderr or result.stdout)[:1000]
                    return Result(problem_dir, "compile_error", e)
                return Result(problem_dir, "compiled", "cf_stdio_main_harness_preserved")
            return Result(problem_dir, "generated", "cf_stdio_main_harness_preserved")

    try:
        harness_src = render_harness(code_rs.read_text(), sig, embed_code=True)
    except Exception as e:
        return Result(problem_dir, "error", f"render_harness: {e}")

    harness_rs.write_text(harness_src)

    if do_compile:
        err = compile_cf_main_bin(problem_dir)
        if err:
            return Result(problem_dir, "compile_error", err)
        harness_bin = tests_dir / "harness_bin"
        result = subprocess.run(
            ["rustc", str(harness_rs), "-o", str(harness_bin), "-O"],
            capture_output=True, text=True, timeout=120,
        )
        if result.returncode != 0:
            e = (result.stderr or result.stdout)[:1000]
            return Result(problem_dir, "compile_error", e)
        return Result(problem_dir, "compiled", f"Solution::{sig.method}")

    return Result(problem_dir, "generated", f"Solution::{sig.method}")


def build_reference_oracle_bin(
    problem_dir: Path,
    *,
    force: bool = False,
    compile_timeout: int = 120,
) -> tuple[Path | None, str]:
    """
    Write ``tests/reference_oracle.rs`` (same JSON contract as ``harness.rs``) with
    ``include!(\"../code.rs\")`` instead of inlined sources, then ``rustc`` to
    ``tests/reference_oracle_bin``.
    """
    code_path = problem_dir / "code.rs"
    if not code_path.exists():
        return None, "missing code.rs"
    tests_dir = problem_dir / "tests"
    tests_dir.mkdir(parents=True, exist_ok=True)
    oracle_rs = tests_dir / REFERENCE_ORACLE_RS_NAME
    oracle_bin = tests_dir / REFERENCE_ORACLE_BIN_NAME

    if oracle_rs.exists():
        otxt = oracle_rs.read_text()
        if (
            "extract_input_stdin" in otxt
            or "run_cf_main_stdin" in otxt
            or "extract_cf_io_input" in otxt
        ):
            err = compile_cf_main_bin(problem_dir, compile_timeout=compile_timeout)
            if err:
                return None, err
            if not force and oracle_bin.exists():
                try:
                    m_main = (problem_dir / "main.rs").stat().st_mtime
                    if (
                        code_path.stat().st_mtime <= oracle_bin.stat().st_mtime
                        and m_main <= oracle_bin.stat().st_mtime
                    ):
                        return oracle_bin, ""
                except OSError:
                    pass
            result = subprocess.run(
                ["rustc", str(oracle_rs), "-o", str(oracle_bin), "-O"],
                capture_output=True,
                text=True,
                timeout=compile_timeout,
            )
            if result.returncode != 0:
                err2 = (result.stderr or result.stdout or "").strip()[:4000]
                return None, err2 or "rustc reference_oracle failed"
            return oracle_bin, ""

    text = code_path.read_text()
    target_name = find_main_fn_name(problem_dir)
    try:
        sig = parse_signature(text, target_name)
    except Exception as e:
        return None, f"parse_signature: {e}"
    structs = extract_structs(text)
    try:
        src = render_harness(text, sig, structs, embed_code=False)
    except Exception as e:
        return None, f"render_harness: {e}"

    if not force and oracle_bin.exists():
        try:
            if code_path.stat().st_mtime <= oracle_bin.stat().st_mtime:
                return oracle_bin, ""
        except OSError:
            pass

    oracle_rs.write_text(src)

    err = compile_cf_main_bin(problem_dir, compile_timeout=compile_timeout)
    if err:
        return None, err

    result = subprocess.run(
        ["rustc", str(oracle_rs), "-o", str(oracle_bin), "-O"],
        capture_output=True,
        text=True,
        timeout=compile_timeout,
    )
    if result.returncode != 0:
        err = (result.stderr or result.stdout or "").strip()[:4000]
        return None, err or "rustc reference_oracle failed"
    return oracle_bin, ""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--problem", type=Path, help="path to a single problem directory")
    g.add_argument("--all", action="store_true", help="build harness for every problem")
    ap.add_argument("--kind", choices=("leetcode", "codeforces", "both"),
                    default="both")
    ap.add_argument("--compile", action="store_true",
                    help="also compile harness with rustc")
    args = ap.parse_args()

    problems = [args.problem.resolve()] if args.problem else iter_problems(args.kind)
    if not problems:
        print("no problems found", file=sys.stderr)
        return 1

    counts: dict[str, int] = {}
    detail_lines: list[str] = []
    for p in problems:
        r = build_one(p, args.compile)
        counts[r.status] = counts.get(r.status, 0) + 1
        if r.status in ("generated", "compiled", "error", "compile_error"):
            if r.status in ("error", "compile_error"):
                detail_lines.append(f"[{r.status}] {p.name}  {r.detail[:100]}")

    for line in detail_lines:
        print(line)
    if detail_lines:
        print()
    print("Summary:")
    for k in ("generated", "compiled", "compile_error", "skipped_no_code", "error"):
        if counts.get(k):
            print(f"  {k:24s} {counts[k]}")
    return 0 if counts.get("error", 0) == 0 and counts.get("compile_error", 0) == 0 else 2


if __name__ == "__main__":
    sys.exit(main())
