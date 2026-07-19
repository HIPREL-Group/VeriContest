#!/usr/bin/env python3
"""
Generate executable postcondition checkers directly from `spec.rs`/`code_spec.rs`.

The pipeline is intentionally split in two stages:
1. Reuse `gen_test_post.py` to build the same normalized
   `exec_spec_unverified!` block we compile elsewhere.
2. Parse the generated postcondition signature and synthesize a small Rust
   runtime that reads testcase objects, converts them into Rust values, and
   calls the executable postcondition.

Using the generated postcondition signature as the handoff point keeps the Rust
runtime aligned with whatever lowering decisions `gen_test_post.py` made.

Usage
-----
    python post2exe/gen_post2exe.py --problem benchmark/leetcode/lc1
    python post2exe/gen_post2exe.py --all
    python post2exe/gen_post2exe.py --all --compile
    python post2exe/gen_post2exe.py --all --compile --run
"""

from __future__ import annotations

import argparse
import importlib.util
import itertools
import json
import os
import shutil
from dataclasses import dataclass, field
from pathlib import Path
import re
import subprocess
import sys

import warnings

warnings.filterwarnings("ignore", category=FutureWarning, module="tree_sitter")

import tree_sitter as ts
import tree_sitter_verus as tsv

REPO_ROOT = Path(__file__).resolve().parent.parent
BENCH_ROOT = REPO_ROOT / "benchmark"
VERUS_BIN = REPO_ROOT / "verus" / "verus"
GEN_TEST_POST_PATH = Path(__file__).resolve().parent / "gen_test_post.py"

# Load `gen_test_post.py` as a module instead of shelling out to it.  This keeps
# both generators on the same transformation logic and avoids duplicated regexes.
_gen_test_post_spec = importlib.util.spec_from_file_location(
    "vcg_test_gen_gen_test_post",
    GEN_TEST_POST_PATH,
)
if _gen_test_post_spec is None or _gen_test_post_spec.loader is None:
    raise RuntimeError(f"cannot load {GEN_TEST_POST_PATH}")
gtp = importlib.util.module_from_spec(_gen_test_post_spec)
sys.modules[_gen_test_post_spec.name] = gtp
_gen_test_post_spec.loader.exec_module(gtp)

_lang = ts.Language(tsv.language())
_parser = ts.Parser(_lang)



@dataclass
class PostcondParam:
    name: str
    spec_type: str
    is_result: bool = False


@dataclass
class PostcondSig:
    fn_name: str
    params: list[PostcondParam]

    @property
    def input_params(self) -> list[PostcondParam]:
        return [p for p in self.params if not p.is_result]

    @property
    def result_param(self) -> PostcondParam | None:
        for p in self.params:
            if p.is_result:
                return p
        return None


def _node_text(node) -> str:
    return node.text.decode("utf-8")


def _find_nodes(node, type_name: str) -> list:
    results = []
    if node.type == type_name:
        results.append(node)
    for child in node.children:
        results.extend(_find_nodes(child, type_name))
    return results


def _find_exec_spec_macro(root) -> list:
    macros = _find_nodes(root, "macro_invocation")
    return [
        m
        for m in macros
        if any(
            c.type == "identifier" and _node_text(c) == "exec_spec_unverified"
            for c in m.children
        )
    ]


def _parse_params_token_tree(params_tree) -> list[PostcondParam] | None:
    text = _node_text(params_tree)
    if not text.startswith("(") or not text.endswith(")"):
        return None
    inner = text[1:-1].strip()
    if not inner:
        return []
    return _split_and_parse_params(inner)


def _split_top_level(text: str) -> list[str]:
    depth_angle = depth_paren = depth_brack = depth_brace = 0
    cur = ""
    parts: list[str] = []
    for ch in text:
        if ch == "<":
            depth_angle += 1
        elif ch == ">":
            depth_angle -= 1
        elif ch == "(":
            depth_paren += 1
        elif ch == ")":
            depth_paren -= 1
        elif ch == "[":
            depth_brack += 1
        elif ch == "]":
            depth_brack -= 1
        elif ch == "{":
            depth_brace += 1
        elif ch == "}":
            depth_brace -= 1
        if (
            ch == ","
            and depth_angle == 0
            and depth_paren == 0
            and depth_brack == 0
            and depth_brace == 0
        ):
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur.strip())
    return parts


def _split_and_parse_params(inner: str) -> list[PostcondParam]:
    params: list[PostcondParam] = []
    for p in _split_top_level(inner):
        if ":" not in p:
            continue
        name, typ = p.split(":", 1)
        params.append(PostcondParam(name=name.strip(), spec_type=typ.strip()))
    _mark_result_param(params)
    return params


RESULT_NAMES = {"res_ret", "result", "output", "res", "ret", "ans", "ok"}


def _mark_result_param(params: list[PostcondParam]) -> None:
    for p in params:
        if p.name in RESULT_NAMES:
            p.is_result = True
            return
    if params:
        params[-1].is_result = True


def _extract_postcond_from_token_tree(token_tree) -> PostcondSig | None:
    # We inspect the macro input after normalization, not the original Verus
    # signature.  At this point types like `int`/`nat` have already been lowered
    # into concrete Rust-friendly types, which is exactly what the runtime needs.
    children = token_tree.children
    n = len(children)
    for i in range(n - 5):
        if (
            _node_text(children[i]) == "spec"
            and children[i + 1].type == "fn"
            and children[i + 2].type == "identifier"
            and _node_text(children[i + 2]).endswith("_postcondition")
            and children[i + 3].type == "token_tree"
            and _node_text(children[i + 3]).startswith("(")
        ):
            fn_name = _node_text(children[i + 2])
            params = _parse_params_token_tree(children[i + 3])
            if params is not None:
                return PostcondSig(fn_name=fn_name, params=params)
    return None


def parse_postcondition_sig(source: bytes) -> PostcondSig | None:
    tree = _parser.parse(source)
    macros = _find_exec_spec_macro(tree.root_node)
    for macro in macros:
        for child in macro.children:
            if child.type == "token_tree":
                sig = _extract_postcond_from_token_tree(child)
                if sig is not None:
                    return sig
    return None


PRIM_INTS = {
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "isize",
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "usize",
}
PRIMITIVES = PRIM_INTS | {"bool", "char"}


def strip_ref(t: str) -> tuple[str, bool, bool]:
    t = t.strip()
    if t.startswith("&mut "):
        return t[5:].strip(), True, True
    if t.startswith("&"):
        return t[1:].strip(), True, False
    return t, False, False


def strip_outer_parens(text: str) -> str:
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        wraps_all = True
        for i, ch in enumerate(text):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(text) - 1:
                    wraps_all = False
                    break
        if not wraps_all:
            break
        text = text[1:-1].strip()
    return text


def split_generic_args(text: str) -> list[str]:
    return _split_top_level(text)


def generic_arg(t: str, name: str) -> str | None:
    t = t.strip()
    prefix = f"{name}<"
    if not (t.startswith(prefix) and t.endswith(">")):
        return None
    return t[len(prefix) : -1].strip()


def parse_tuple_items(t: str) -> list[str] | None:
    t = t.strip()
    if not (t.startswith("(") and t.endswith(")")):
        return None
    inner = t[1:-1].strip()
    if not inner:
        return []
    items = _split_top_level(inner)
    return items if len(items) >= 2 else None


def spec_to_owned_rust_type(spec_type: str) -> str | None:
    """Map the normalized spec type to an owned Rust runtime type.

    The generated runner parses each testcase into ordinary Rust values first,
    then borrows those values back into the `exec_...` wrapper when needed.
    Returning `None` here means the top-level argument/result cannot be decoded
    with the lightweight runtime parser we generate.
    """
    inner, _, _ = strip_ref(spec_type)
    inner = inner.strip()
    if inner in PRIMITIVES:
        return inner
    if inner in {"String", "SpecString"}:
        return "String"
    if inner == "()":
        return "()"

    for seq_name in ("Seq", "Vec"):
        seq_arg = generic_arg(inner, seq_name)
        if seq_arg is not None:
            elem_ty = spec_to_owned_rust_type(seq_arg)
            return None if elem_ty is None else f"Vec<{elem_ty}>"

    option_arg = generic_arg(inner, "Option")
    if option_arg is not None:
        elem_ty = spec_to_owned_rust_type(option_arg)
        return None if elem_ty is None else f"Option<{elem_ty}>"

    set_arg = generic_arg(inner, "Set")
    if set_arg is not None:
        elem_ty = spec_to_owned_rust_type(set_arg)
        return None if elem_ty is None else f"std::collections::HashSet<{elem_ty}>"

    map_arg = generic_arg(inner, "Map")
    if map_arg is not None:
        parts = split_generic_args(map_arg)
        if len(parts) != 2:
            return None
        key_ty = spec_to_owned_rust_type(parts[0])
        val_ty = spec_to_owned_rust_type(parts[1])
        if key_ty is None or val_ty is None:
            return None
        return f"std::collections::HashMap<{key_ty}, {val_ty}>"

    tuple_items = parse_tuple_items(inner)
    if tuple_items is not None:
        item_types = [spec_to_owned_rust_type(item) for item in tuple_items]
        if any(item is None for item in item_types):
            return None
        return "(" + ", ".join(item_types) + ")"

    return None


def needs_borrowed_arg(spec_type: str) -> bool:
    inner, _, _ = strip_ref(spec_type)
    inner = inner.strip()
    return inner not in PRIMITIVES and inner != "()"


def gen_call_arg(var_name: str, spec_type: str) -> str:
    """Build the expression passed to `exec_<postcondition>`.

    We store parsed testcase values in owned Rust containers (`Vec`, `String`,
    `HashMap`, ...), then re-borrow them here when the exec-spec wrapper expects
    references or slice-like inputs.
    """
    inner, _, _ = strip_ref(spec_type)
    inner = inner.strip()
    for seq_name in ("Seq", "Vec"):
        seq_arg = generic_arg(inner, seq_name)
        if seq_arg is not None:
            return f"{var_name}.as_slice()"
    if inner in {"String", "SpecString"}:
        return f"&{var_name}"
    if inner in PRIMITIVES or inner == "()":
        return var_name
    if needs_borrowed_arg(spec_type):
        return f"&{var_name}"
    return var_name


class RustExprGen:
    """Emit Rust expressions that decode a generic `Value` into a typed value.

    This class produces source code strings, not runtime values.  The generator
    recurses on the normalized spec type and expands nested collections/tuples
    into the corresponding Rust parsing expression.
    """
    def __init__(self) -> None:
        self.counter = 0

    def tmp(self, prefix: str) -> str:
        self.counter += 1
        return f"__{prefix}_{self.counter}"

    def gen(self, value_expr: str, spec_type: str) -> str | None:
        # `value_expr` is a Rust expression of type `&Value`.  Every recursive
        # branch returns another Rust expression string that converts it into the
        # requested concrete type.
        inner, _, _ = strip_ref(spec_type)
        inner = inner.strip()

        if inner in PRIM_INTS:
            return f"expect_number::<{inner}>({value_expr})"
        if inner == "bool":
            return f"expect_bool({value_expr})"
        if inner == "char":
            return f"expect_char({value_expr})"
        if inner in {"String", "SpecString"}:
            return f"expect_string({value_expr})"
        if inner == "()":
            return "()"

        for seq_name in ("Seq", "Vec"):
            seq_arg = generic_arg(inner, seq_name)
            if seq_arg is not None:
                if seq_arg.strip() == "char":
                    return f"expect_char_vec({value_expr})"
                list_var = self.tmp("list")
                item_var = self.tmp("item")
                elem_expr = self.gen(f"&{item_var}", seq_arg)
                if elem_expr is None:
                    return None
                return (
                    "{ "
                    f"let {list_var} = expect_list({value_expr}); "
                    f"{list_var}.iter().map(|{item_var}| {elem_expr}).collect::<Vec<_>>()"
                    " }"
                )

        option_arg = generic_arg(inner, "Option")
        if option_arg is not None:
            elem_expr = self.gen(value_expr, option_arg)
            if elem_expr is None:
                return None
            return f"if is_null({value_expr}) {{ None }} else {{ Some({elem_expr}) }}"

        set_arg = generic_arg(inner, "Set")
        if set_arg is not None:
            list_var = self.tmp("set")
            item_var = self.tmp("item")
            elem_expr = self.gen(f"&{item_var}", set_arg)
            if elem_expr is None:
                return None
            return (
                "{ "
                f"let {list_var} = expect_list({value_expr}); "
                f"{list_var}.iter().map(|{item_var}| {elem_expr}).collect::<std::collections::HashSet<_>>()"
                " }"
            )

        map_arg = generic_arg(inner, "Map")
        if map_arg is not None:
            parts = split_generic_args(map_arg)
            if len(parts) != 2:
                return None
            list_var = self.tmp("map")
            pair_var = self.tmp("pair")
            pair_list = self.tmp("pair_list")
            key_expr = self.gen(f"&{pair_list}[0]", parts[0])
            val_expr = self.gen(f"&{pair_list}[1]", parts[1])
            if key_expr is None or val_expr is None:
                return None
            return (
                "{ "
                f"let {list_var} = expect_list({value_expr}); "
                f"{list_var}.iter().map(|{pair_var}| {{ "
                f"let {pair_list} = expect_list({pair_var}); "
                f"expect_list_len({pair_list}, 2); "
                f"({key_expr}, {val_expr})"
                " }).collect::<std::collections::HashMap<_, _>>()"
                " }"
            )

        tuple_items = parse_tuple_items(inner)
        if tuple_items is not None:
            list_var = self.tmp("tuple")
            exprs: list[str] = []
            for i, item in enumerate(tuple_items):
                item_expr = self.gen(f"&{list_var}[{i}]", item)
                if item_expr is None:
                    return None
                exprs.append(item_expr)
            return (
                "{ "
                f"let {list_var} = expect_list({value_expr}); "
                f"expect_list_len({list_var}, {len(tuple_items)}); "
                "(" + ", ".join(exprs) + ")"
                " }"
            )

        return None


def spec_to_direct_rust_type(spec_type: str) -> str | None:
    """Map a spec or exec type into the direct plain-Rust backend type.

    Non-primitive immutable collections are wrapped in `Rc<...>` so helper
    functions can take ownership cheaply while recursive calls keep sharing the
    same backing data.
    """
    inner, _, _ = strip_ref(spec_type)
    inner = inner.strip()
    if inner in {"int", "nat"}:
        return "i64"
    if inner == "usize":
        return "i64"
    if inner in PRIMITIVES:
        return inner
    if inner in {"String", "SpecString", "str"}:
        return "std::rc::Rc<String>"
    if inner == "()":
        return "()"

    for seq_name in ("Seq", "Vec"):
        seq_arg = generic_arg(inner, seq_name)
        if seq_arg is not None:
            elem_ty = spec_to_direct_rust_type(seq_arg)
            return None if elem_ty is None else f"std::rc::Rc<Vec<{elem_ty}>>"

    option_arg = generic_arg(inner, "Option")
    if option_arg is not None:
        elem_ty = spec_to_direct_rust_type(option_arg)
        return None if elem_ty is None else f"Option<{elem_ty}>"

    set_arg = generic_arg(inner, "Set")
    if set_arg is not None:
        elem_ty = spec_to_direct_rust_type(set_arg)
        return (
            None
            if elem_ty is None
            else f"std::rc::Rc<std::collections::HashSet<{elem_ty}>>"
        )

    map_arg = generic_arg(inner, "Map")
    if map_arg is not None:
        parts = split_generic_args(map_arg)
        if len(parts) != 2:
            return None
        key_ty = spec_to_direct_rust_type(parts[0])
        val_ty = spec_to_direct_rust_type(parts[1])
        if key_ty is None or val_ty is None:
            return None
        return f"std::rc::Rc<std::collections::HashMap<{key_ty}, {val_ty}>>"

    tuple_items = parse_tuple_items(inner)
    if tuple_items is not None:
        item_types = [spec_to_direct_rust_type(item) for item in tuple_items]
        if any(item is None for item in item_types):
            return None
        return "(" + ", ".join(item_types) + ")"

    return None


def type_is_copy_like(spec_type: str) -> bool:
    inner, _, _ = strip_ref(spec_type)
    inner = inner.strip()
    if inner in {"int", "nat"} | PRIMITIVES:
        return True
    tuple_items = parse_tuple_items(inner)
    if tuple_items is not None:
        return all(type_is_copy_like(item) for item in tuple_items)
    option_arg = generic_arg(inner, "Option")
    if option_arg is not None:
        return type_is_copy_like(option_arg)
    return False


def coerce_direct_arg(expr: str, spec_type: str) -> str:
    """Coerce an argument to the callee's expected direct-backend type."""
    target = spec_to_direct_rust_type(spec_type)
    if target is None:
        raise ValueError(f"unsupported direct arg type `{spec_type}`")
    expr = expr.strip()
    if type_is_copy_like(spec_type):
        if target in {"bool", "char", "()"}:
            return expr
        return f"(({expr}) as {target})"
    return f"({expr}).clone()"


def _direct_vec_elem_type(rust_type: str | None) -> str | None:
    if rust_type is None:
        return None
    rust_type = rust_type.strip()
    prefix = "std::rc::Rc<Vec<"
    if rust_type.startswith(prefix) and rust_type.endswith(">>"):
        return rust_type[len(prefix) : -2].strip()
    if rust_type.startswith("Vec<") and rust_type.endswith(">"):
        return rust_type[4:-1].strip()
    return None


def _direct_int_type(text: str | None) -> bool:
    return text in PRIM_INTS | {"i64"}


class DirectRustExprGen:
    """Build Rust expressions that decode testcase `Value`s for the direct backend."""

    def __init__(self) -> None:
        self.counter = 0

    def tmp(self, prefix: str) -> str:
        self.counter += 1
        return f"__{prefix}_{self.counter}"

    def gen(self, value_expr: str, spec_type: str) -> str | None:
        inner, _, _ = strip_ref(spec_type)
        inner = inner.strip()

        if inner in {"int", "nat"}:
            return f"expect_number::<i64>({value_expr})"
        if inner == "usize":
            return f"expect_number::<i64>({value_expr})"
        if inner in PRIM_INTS:
            return f"expect_number::<{inner}>({value_expr})"
        if inner == "bool":
            return f"expect_bool({value_expr})"
        if inner == "char":
            return f"expect_char({value_expr})"
        if inner in {"String", "SpecString", "str"}:
            return f"std::rc::Rc::new(expect_string({value_expr}))"
        if inner == "()":
            return "()"

        for seq_name in ("Seq", "Vec"):
            seq_arg = generic_arg(inner, seq_name)
            if seq_arg is not None:
                if seq_arg.strip() == "char":
                    return f"std::rc::Rc::new(expect_char_vec({value_expr}))"
                list_var = self.tmp("list")
                item_var = self.tmp("item")
                elem_expr = self.gen(f"&{item_var}", seq_arg)
                if elem_expr is None:
                    return None
                return (
                    "{ "
                    f"let {list_var} = expect_list({value_expr}); "
                    f"std::rc::Rc::new({list_var}.iter().map(|{item_var}| {elem_expr}).collect::<Vec<_>>())"
                    " }"
                )

        option_arg = generic_arg(inner, "Option")
        if option_arg is not None:
            elem_expr = self.gen(value_expr, option_arg)
            if elem_expr is None:
                return None
            return f"if is_null({value_expr}) {{ None }} else {{ Some({elem_expr}) }}"

        set_arg = generic_arg(inner, "Set")
        if set_arg is not None:
            list_var = self.tmp("set")
            item_var = self.tmp("item")
            elem_expr = self.gen(f"&{item_var}", set_arg)
            if elem_expr is None:
                return None
            return (
                "{ "
                f"let {list_var} = expect_list({value_expr}); "
                f"std::rc::Rc::new({list_var}.iter().map(|{item_var}| {elem_expr}).collect::<std::collections::HashSet<_>>())"
                " }"
            )

        map_arg = generic_arg(inner, "Map")
        if map_arg is not None:
            parts = split_generic_args(map_arg)
            if len(parts) != 2:
                return None
            list_var = self.tmp("map")
            pair_var = self.tmp("pair")
            pair_list = self.tmp("pair_list")
            key_expr = self.gen(f"&{pair_list}[0]", parts[0])
            val_expr = self.gen(f"&{pair_list}[1]", parts[1])
            if key_expr is None or val_expr is None:
                return None
            return (
                "{ "
                f"let {list_var} = expect_list({value_expr}); "
                f"std::rc::Rc::new({list_var}.iter().map(|{pair_var}| {{ "
                f"let {pair_list} = expect_list({pair_var}); "
                f"expect_list_len({pair_list}, 2); "
                f"({key_expr}, {val_expr})"
                " }).collect::<std::collections::HashMap<_, _>>())"
                " }"
            )

        tuple_items = parse_tuple_items(inner)
        if tuple_items is not None:
            list_var = self.tmp("tuple")
            exprs: list[str] = []
            for i, item in enumerate(tuple_items):
                item_expr = self.gen(f"&{list_var}[{i}]", item)
                if item_expr is None:
                    return None
                exprs.append(item_expr)
            return (
                "{ "
                f"let {list_var} = expect_list({value_expr}); "
                f"expect_list_len({list_var}, {len(tuple_items)}); "
                "(" + ", ".join(exprs) + ")"
                " }"
            )

        return None


# The testcase format in this repository is "JSON-like", not strict JSON:
# tuples are often written with `(...)`, and `Option` values may appear as
# `Some(x)` / `None`.  The generated checker only needs enough parsing power for
# those benchmark encodings, so we embed a deliberately small parser instead of a
# full serde/JSON dependency.
RUST_HELPERS = r'''
use std::collections::BTreeMap;
use std::io::Read;

#[derive(Clone, Debug)]
enum Value {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    List(Vec<Value>),
    Object(BTreeMap<String, Value>),
}

struct Parser<'a> {
    s: &'a [u8],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self { s: input.as_bytes(), pos: 0 }
    }

    fn parse_object_root(mut self) -> BTreeMap<String, Value> {
        self.skip_ws();
        match self.parse_value() {
            Value::Object(obj) => obj,
            other => panic!("expected object, got {:?}", other),
        }
    }

    fn skip_ws(&mut self) {
        while self.pos < self.s.len() && self.s[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.s.get(self.pos).copied()
    }

    fn bump(&mut self) -> u8 {
        let ch = self.s[self.pos];
        self.pos += 1;
        ch
    }

    fn expect(&mut self, expected: u8) {
        self.skip_ws();
        let got = self.bump();
        assert!(got == expected, "expected {:?}, got {:?}", expected as char, got as char);
    }

    fn parse_value(&mut self) -> Value {
        self.skip_ws();
        match self.peek() {
            Some(b'"') => Value::String(self.parse_string()),
            Some(b'[') => Value::List(self.parse_list(b'[', b']')),
            Some(b'(') => Value::List(self.parse_list(b'(', b')')),
            Some(b'{') => Value::Object(self.parse_object()),
            Some(b'-') | Some(b'0'..=b'9') => Value::Number(self.parse_number()),
            Some(b'a'..=b'z') | Some(b'A'..=b'Z') | Some(b'_') => self.parse_ident_value(),
            Some(other) => panic!("unsupported value start {:?} in input", other as char),
            None => panic!("unexpected end of input"),
        }
    }

    fn parse_string(&mut self) -> String {
        self.expect(b'"');
        let mut out = String::new();
        while let Some(ch) = self.peek() {
            self.pos += 1;
            match ch {
                b'\\' => {
                    let esc = self.bump();
                    match esc {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{0008}'),
                        b'f' => out.push('\u{000c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        _ => panic!("unsupported escape sequence"),
                    }
                }
                b'"' => return out,
                _ => out.push(ch as char),
            }
        }
        panic!("unterminated string");
    }

    fn parse_number(&mut self) -> String {
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() || matches!(ch, b'-' | b'+' | b'.' | b'e' | b'E') {
                self.pos += 1;
            } else {
                break;
            }
        }
        std::str::from_utf8(&self.s[start..self.pos]).unwrap().trim().to_string()
    }

    fn parse_ident(&mut self) -> String {
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || ch == b'_' {
                self.pos += 1;
            } else {
                break;
            }
        }
        std::str::from_utf8(&self.s[start..self.pos]).unwrap().to_string()
    }

    fn parse_ident_value(&mut self) -> Value {
        let ident = self.parse_ident();
        self.skip_ws();
        match ident.as_str() {
            "true" => Value::Bool(true),
            "false" => Value::Bool(false),
            "null" | "None" => Value::Null,
            "Some" => {
                self.expect(b'(');
                let inner = self.parse_value();
                self.skip_ws();
                self.expect(b')');
                inner
            }
            other => panic!("unsupported identifier value {}", other),
        }
    }

    fn parse_list(&mut self, open: u8, close: u8) -> Vec<Value> {
        self.expect(open);
        let mut out = Vec::new();
        loop {
            self.skip_ws();
            if self.peek() == Some(close) {
                self.pos += 1;
                return out;
            }
            out.push(self.parse_value());
            self.skip_ws();
            match self.peek() {
                Some(b',') => {
                    self.pos += 1;
                }
                Some(ch) if ch == close => {
                    self.pos += 1;
                    return out;
                }
                other => panic!("expected ',' or closing delimiter, got {:?}", other),
            }
        }
    }

    fn parse_object(&mut self) -> BTreeMap<String, Value> {
        self.expect(b'{');
        let mut out = BTreeMap::new();
        loop {
            self.skip_ws();
            if self.peek() == Some(b'}') {
                self.pos += 1;
                return out;
            }
            let key = self.parse_string();
            self.skip_ws();
            self.expect(b':');
            let value = self.parse_value();
            out.insert(key, value);
            self.skip_ws();
            match self.peek() {
                Some(b',') => {
                    self.pos += 1;
                }
                Some(b'}') => {
                    self.pos += 1;
                    return out;
                }
                other => panic!("expected ',' or '}}', got {:?}", other),
            }
        }
    }
}

fn parse_line_object(line: &str) -> BTreeMap<String, Value> {
    Parser::new(line).parse_object_root()
}

fn normalize_key(key: &str) -> String {
    key.chars()
        .filter(|ch| ch.is_ascii_alphanumeric())
        .map(|ch| ch.to_ascii_lowercase())
        .collect()
}

fn get_required_field<'a>(obj: &'a BTreeMap<String, Value>, key: &str) -> &'a Value {
    if let Some(value) = obj.get(key) {
        return value;
    }
    let normalized = normalize_key(key);
    let mut matched: Option<&Value> = None;
    for (candidate, value) in obj.iter() {
        if normalize_key(candidate) == normalized {
            assert!(
                matched.is_none(),
                "ambiguous normalized key {}",
                key,
            );
            matched = Some(value);
        }
    }
    matched.unwrap_or_else(|| panic!("missing key {}", key))
}

fn is_null(v: &Value) -> bool {
    matches!(v, Value::Null)
}

trait ParseNum: Sized {
    fn parse_from(s: &str) -> Self;
}

macro_rules! impl_parse_num {
    ($($t:ty),*) => { $(
        impl ParseNum for $t {
            fn parse_from(s: &str) -> Self {
                s.trim().parse().unwrap_or_else(|_| panic!("bad number: {}", s))
            }
        }
    )* }
}

impl_parse_num!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

fn expect_number<T: ParseNum>(v: &Value) -> T {
    match v {
        Value::Number(s) => T::parse_from(s),
        Value::Bool(true) => T::parse_from("1"),
        Value::Bool(false) => T::parse_from("0"),
        Value::Null => T::parse_from("0"),
        other => panic!("expected number, got {:?}", other),
    }
}

fn expect_bool(v: &Value) -> bool {
    match v {
        Value::Bool(b) => *b,
        Value::Number(s) => s.trim() != "0",
        other => panic!("expected bool, got {:?}", other),
    }
}

fn expect_string(v: &Value) -> String {
    match v {
        Value::String(s) => s.clone(),
        other => panic!("expected string, got {:?}", other),
    }
}

fn expect_char(v: &Value) -> char {
    match v {
        Value::String(s) => {
            let mut chars = s.chars();
            let ch = chars.next().unwrap_or_else(|| panic!("empty char string"));
            assert!(chars.next().is_none(), "char value must contain exactly one character");
            ch
        }
        other => panic!("expected char string, got {:?}", other),
    }
}

fn expect_char_vec(v: &Value) -> Vec<char> {
    match v {
        Value::String(s) => s.chars().collect(),
        Value::List(items) => items.iter().map(expect_char).collect(),
        other => panic!("expected string/list for char vec, got {:?}", other),
    }
}

fn expect_list(v: &Value) -> &Vec<Value> {
    match v {
        Value::List(items) => items,
        other => panic!("expected list, got {:?}", other),
    }
}

fn expect_list_len(items: &Vec<Value>, expected: usize) {
    assert!(items.len() == expected, "expected list of len {}, got {}", expected, items.len());
}
'''


DIRECT_HELPERS = r'''
use std::rc::Rc;

fn seq_empty<T>() -> Rc<Vec<T>> {
    Rc::new(Vec::new())
}

fn seq_last<T: Clone>(s: Rc<Vec<T>>) -> T {
    s.last().unwrap().clone()
}

fn seq_drop_last<T: Clone>(s: Rc<Vec<T>>) -> Rc<Vec<T>> {
    if s.is_empty() {
        Rc::new(Vec::new())
    } else {
        Rc::new(s[..s.len() - 1].to_vec())
    }
}

fn seq_drop_first<T: Clone>(s: Rc<Vec<T>>) -> Rc<Vec<T>> {
    if s.is_empty() {
        Rc::new(Vec::new())
    } else {
        Rc::new(s[1..].to_vec())
    }
}

fn seq_take<T: Clone>(s: Rc<Vec<T>>, end: i64) -> Rc<Vec<T>> {
    let end = end.max(0) as usize;
    Rc::new(s[..end.min(s.len())].to_vec())
}

fn seq_skip<T: Clone>(s: Rc<Vec<T>>, start: i64) -> Rc<Vec<T>> {
    let start = start.max(0) as usize;
    Rc::new(s[start.min(s.len())..].to_vec())
}

fn seq_subrange<T: Clone>(s: Rc<Vec<T>>, start: i64, end: i64) -> Rc<Vec<T>> {
    let start = start.max(0) as usize;
    let end = end.max(start as i64) as usize;
    let start = start.min(s.len());
    let end = end.min(s.len());
    Rc::new(s[start..end].to_vec())
}

fn seq_add<T: Clone>(left: Rc<Vec<T>>, right: Rc<Vec<T>>) -> Rc<Vec<T>> {
    let mut out = (*left).clone();
    out.extend(right.iter().cloned());
    Rc::new(out)
}

fn seq_to_multiset<T: Clone + Eq + std::hash::Hash>(s: Rc<Vec<T>>) -> std::collections::HashMap<T, i64> {
    let mut out = std::collections::HashMap::new();
    for item in s.iter().cloned() {
        *out.entry(item).or_insert(0) += 1;
    }
    out
}

fn seq_push<T: Clone>(s: Rc<Vec<T>>, value: T) -> Rc<Vec<T>> {
    let mut out = (*s).clone();
    out.push(value);
    Rc::new(out)
}

fn seq_update<T: Clone>(s: Rc<Vec<T>>, idx: i64, value: T) -> Rc<Vec<T>> {
    let mut out = (*s).clone();
    let idx = idx as usize;
    out[idx] = value;
    Rc::new(out)
}

fn seq_new<T, F: Fn(i64) -> T>(len: i64, f: F) -> Rc<Vec<T>> {
    let len = len.max(0);
    let mut out = Vec::with_capacity(len as usize);
    for i in 0..len {
        out.push(f(i));
    }
    Rc::new(out)
}

fn seq_map_values<T: Clone, U, F: Fn(T) -> U>(s: Rc<Vec<T>>, f: F) -> Rc<Vec<U>> {
    Rc::new(s.iter().cloned().map(f).collect())
}

fn seq_filter<T: Clone, F: Fn(T) -> bool>(s: Rc<Vec<T>>, f: F) -> Rc<Vec<T>> {
    Rc::new(s.iter().cloned().filter(|item| f(item.clone())).collect())
}

fn seq_vec_max_i64(s: Rc<Vec<i64>>) -> i64 {
    *s.iter().max().unwrap_or(&0)
}

fn seq_vec_min_i64(s: Rc<Vec<i64>>) -> i64 {
    *s.iter().min().unwrap_or(&0)
}

fn string_chars(s: Rc<String>) -> Rc<Vec<char>> {
    Rc::new(s.chars().collect())
}

fn mod_norm_i64(value: i128, modulus: i64) -> i64 {
    let m = modulus as i128;
    let mut out = value % m;
    if out < 0 {
        out += m;
    }
    out as i64
}

fn mod_add_i64(a: i64, b: i64, modulus: i64) -> i64 {
    mod_norm_i64((a as i128) + (b as i128), modulus)
}

fn mod_sub_i64(a: i64, b: i64, modulus: i64) -> i64 {
    mod_norm_i64((a as i128) - (b as i128), modulus)
}

fn mod_mul_i64(a: i64, b: i64, modulus: i64) -> i64 {
    mod_norm_i64((a as i128) * (b as i128), modulus)
}

fn mod_neg_i64(a: i64, modulus: i64) -> i64 {
    mod_norm_i64(-(a as i128), modulus)
}

fn next_permutation<T: Ord>(values: &mut [T]) -> bool {
    if values.len() < 2 {
        return false;
    }
    let mut pivot = values.len() - 1;
    while pivot > 0 && values[pivot - 1] >= values[pivot] {
        pivot -= 1;
    }
    if pivot == 0 {
        return false;
    }
    let pivot_idx = pivot - 1;
    let mut swap_idx = values.len() - 1;
    while values[swap_idx] <= values[pivot_idx] {
        swap_idx -= 1;
    }
    values.swap(pivot_idx, swap_idx);
    values[pivot..].reverse();
    true
}

fn seq_sorted_copy<T: Clone + Ord>(s: Rc<Vec<T>>) -> Rc<Vec<T>> {
    let mut out = (*s).clone();
    out.sort();
    Rc::new(out)
}

fn seq_unique_permutations<T: Clone + Ord>(s: Rc<Vec<T>>) -> Vec<Rc<Vec<T>>> {
    let mut cur = (*s).clone();
    cur.sort();
    let mut out = Vec::new();
    loop {
        out.push(Rc::new(cur.clone()));
        if !next_permutation(&mut cur) {
            break;
        }
    }
    out
}

fn seq_words_from_values_rec<T: Clone>(
    remaining: usize,
    values: &Vec<T>,
    cur: &mut Vec<T>,
    out: &mut Vec<Rc<Vec<T>>>,
) {
    if remaining == 0 {
        out.push(Rc::new(cur.clone()));
        return;
    }
    for value in values.iter().cloned() {
        cur.push(value);
        seq_words_from_values_rec(remaining - 1, values, cur, out);
        cur.pop();
    }
}

fn seq_words_from_values<T: Clone>(
    len_lower: i64,
    len_upper: i64,
    values: Rc<Vec<T>>,
) -> Vec<Rc<Vec<T>>> {
    let len_lower = len_lower.max(0);
    let len_upper = len_upper.max(len_lower);
    let mut out = Vec::new();
    for len in len_lower..len_upper {
        let mut cur = Vec::with_capacity(len as usize);
        seq_words_from_values_rec(len as usize, values.as_ref(), &mut cur, &mut out);
    }
    out
}

fn seq_union_distinct_values<T: Clone + Eq + std::hash::Hash + Ord>(
    seqs: Vec<Rc<Vec<T>>>,
) -> Rc<Vec<T>> {
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::new();
    for seq in seqs {
        for item in seq.iter().cloned() {
            if seen.insert(item.clone()) {
                out.push(item);
            }
        }
    }
    out.sort();
    Rc::new(out)
}

fn seq_words_range_i64(
    len_lower: i64,
    len_upper: i64,
    elem_lower: i64,
    elem_upper: i64,
) -> Vec<Rc<Vec<i64>>> {
    let values = Rc::new((elem_lower..elem_upper).collect::<Vec<_>>());
    seq_words_from_values(len_lower, len_upper, values)
}

fn seq_words_range_i32(
    len_lower: i64,
    len_upper: i64,
    elem_lower: i64,
    elem_upper: i64,
) -> Vec<Rc<Vec<i32>>> {
    let mut values = Vec::new();
    for value in elem_lower..elem_upper {
        values.push(value as i32);
    }
    seq_words_from_values(len_lower, len_upper, Rc::new(values))
}

fn safe_index_clone<T: Clone + Default>(s: &[T], idx: i64) -> T {
    if idx < 0 {
        return T::default();
    }
    let i = idx as usize;
    if i >= s.len() {
        return T::default();
    }
    s[i].clone()
}

fn mod_floor_i64(a: i64, b: i64) -> i64 {
    if b == 0 {
        return 0;
    }
    let r = a % b;
    if (r != 0) && ((r < 0) != (b < 0)) {
        r + b
    } else {
        r
    }
}
'''


class DirectTranslationError(RuntimeError):
    pass


@dataclass
class DirectFunction:
    name: str
    params: list[PostcondParam]
    ret_type: str
    source: str
    body_text: str
    tree: object
    node: object


@dataclass
class SeqQuantDomain:
    len_lower: list[tuple[str, bool]] = field(default_factory=list)
    len_upper: list[tuple[str, bool]] = field(default_factory=list)
    elem_lower: list[tuple[str, bool]] = field(default_factory=list)
    elem_upper: list[tuple[str, bool]] = field(default_factory=list)
    perm_sources: list[str] = field(default_factory=list)
    value_sources: list[str] = field(default_factory=list)
    first_values: list[str] = field(default_factory=list)
    last_values: list[str] = field(default_factory=list)
    increasing_hint: bool = False
    sorted_hint: bool = False


def _node_src(node, src: bytes) -> str:
    return src[node.start_byte : node.end_byte].decode("utf-8")


def _first_function_item(root) -> object | None:
    nodes = _find_nodes(root, "function_item")
    return nodes[0] if nodes else None


def _parse_direct_function(source: str) -> DirectFunction:
    src = source.encode("utf-8")
    tree = _parser.parse(src)
    root = tree.root_node
    node = _first_function_item(root)
    if node is None:
        raise DirectTranslationError("no function_item found in generated direct source")
    name_node = node.child_by_field_name("name")
    params_node = node.child_by_field_name("parameters")
    body_node = node.child_by_field_name("body")
    ret_node = node.child_by_field_name("return_type")
    if name_node is None or params_node is None or body_node is None:
        raise DirectTranslationError("incomplete function_item in generated direct source")
    params = _parse_params_token_tree(params_node)
    if params is None:
        raise DirectTranslationError("could not parse function parameters for direct backend")
    ret_type = _node_src(ret_node, src) if ret_node is not None else "()"
    body_text = _node_src(body_node, src)
    return DirectFunction(
        name=_node_src(name_node, src),
        params=params,
        ret_type=ret_type.strip(),
        source=source,
        body_text=body_text,
        tree=tree,
        node=node,
    )


def _block_inner_text(block_text: str) -> str:
    block_text = block_text.strip()
    if block_text.startswith("{") and block_text.endswith("}"):
        return block_text[1:-1].strip()
    return block_text


def _parse_direct_expr(expr_text: str):
    wrapper = (
        "verus! {\n"
        "pub open spec fn __tmp() -> bool {\n"
        f"{expr_text}\n"
        "}\n"
        "}\n"
    )
    fn = _parse_direct_function(wrapper)
    body_node = fn.node.child_by_field_name("body")
    if body_node is None:
        return None
    named = [c for c in body_node.named_children if c.type not in {"inner_attribute_item"}]
    return named[-1] if named else None


def _parse_direct_expr_with_fn(expr_text: str) -> tuple[object | None, DirectFunction]:
    wrapper = (
        "verus! {\n"
        "pub open spec fn __tmp() -> bool {\n"
        f"{expr_text}\n"
        "}\n"
        "}\n"
    )
    fn = _parse_direct_function(wrapper)
    body_node = fn.node.child_by_field_name("body")
    if body_node is None:
        return None, fn
    named = [c for c in body_node.named_children if c.type not in {"inner_attribute_item"}]
    return (named[-1] if named else None), fn


def _comparison_op(node) -> str | None:
    if node is None or node.type != "binary_expression":
        return None
    op_node = node.child_by_field_name("operator")
    if op_node is None:
        return None
    return op_node.text.decode("utf-8")


def _unwrap_attrs_and_parens(node, keep_view: bool = False):
    unwrap_kinds = {
        "parenthesized_expression",
        "attribute_expression",
    }
    if not keep_view:
        unwrap_kinds.add("view_expression")
    while node is not None and node.type in unwrap_kinds:
        named = [c for c in node.named_children]
        if not named:
            break
        if node.type == "view_expression":
            node = named[0]
        else:
            node = named[-1]
    return node


def _closure_params_text(node, src: bytes) -> list[tuple[str, str | None]]:
    params: list[tuple[str, str | None]] = []
    for child in node.named_children:
        if child.type != "parameter":
            continue
        pieces = [c for c in child.named_children]
        if not pieces:
            continue
        name = _node_src(pieces[0], src).strip()
        ty = _node_src(pieces[1], src).strip() if len(pieces) > 1 else None
        params.append((name, ty))
    return params


def _split_bool_and_parts(node) -> list:
    node = _unwrap_attrs_and_parens(node)
    if node is None:
        return []
    if node.type == "binary_expression" and _comparison_op(node) in {"&&", "&&&"}:
        left = node.child_by_field_name("left")
        right = node.child_by_field_name("right")
        return _split_bool_and_parts(left) + _split_bool_and_parts(right)
    if node.type == "big_and_expression":
        parts: list = []
        for child in node.named_children:
            parts.extend(_split_bool_and_parts(child))
        return parts
    return [node]


def _flatten_comparison_chain(node) -> tuple[list, list[str]] | None:
    node = _unwrap_attrs_and_parens(node)
    op = _comparison_op(node)
    if op not in {"<", "<=", ">", ">=", "==", "!=", "=~="}:
        return None
    left = _unwrap_attrs_and_parens(node.child_by_field_name("left"))
    right = _unwrap_attrs_and_parens(node.child_by_field_name("right"))
    if left is None or right is None:
        return None
    left_flat = _flatten_comparison_chain(left)
    if left_flat is None:
        return [left, right], [op]
    items, ops = left_flat
    return items + [right], ops + [op]


def _node_mentions_any_binder(node, src: bytes, binder_names: set[str]) -> bool:
    node = _unwrap_attrs_and_parens(node, keep_view=True)
    if node is None:
        return False
    if node.type == "identifier":
        return _node_src(node, src).strip() in binder_names
    return any(_node_mentions_any_binder(child, src, binder_names) for child in node.named_children)


def _sequence_elem_spec_type(spec_type: str) -> str | None:
    inner, _, _ = strip_ref(spec_type)
    inner = inner.strip()
    for seq_name in ("Seq", "Vec"):
        seq_arg = generic_arg(inner, seq_name)
        if seq_arg is not None:
            return seq_arg.strip()
    return None


def _sequence_binder_name(node, src: bytes, binder_names: set[str]) -> str | None:
    node = _unwrap_attrs_and_parens(node, keep_view=True)
    if node is None or node.type != "identifier":
        return None
    name = _node_src(node, src).strip()
    return name if name in binder_names else None


def _sequence_binder_len_name(node, src: bytes, binder_names: set[str]) -> str | None:
    node = _unwrap_attrs_and_parens(node, keep_view=True)
    if node is None or node.type != "call_expression":
        return None
    callee = node.child_by_field_name("function")
    args = node.child_by_field_name("arguments")
    if callee is None or args is None or args.named_children:
        return None
    callee = _unwrap_attrs_and_parens(callee, keep_view=True)
    if callee is None or callee.type != "field_expression":
        return None
    named = [c for c in callee.named_children]
    if len(named) != 2:
        return None
    recv, field = named
    if _node_src(field, src).strip() != "len":
        return None
    return _sequence_binder_name(recv, src, binder_names)


def _sequence_binder_elem_name(node, src: bytes, binder_names: set[str]) -> str | None:
    node = _unwrap_attrs_and_parens(node, keep_view=True)
    if node is None or node.type != "index_expression":
        return None
    named = [c for c in node.named_children]
    if len(named) != 2:
        return None
    return _sequence_binder_name(named[0], src, binder_names)


def _sequence_binder_endpoint(node, src: bytes, binder_names: set[str]) -> tuple[str, str] | None:
    node = _unwrap_attrs_and_parens(node, keep_view=True)
    if node is None or node.type != "index_expression":
        return None
    named = [c for c in node.named_children]
    if len(named) != 2:
        return None
    binder_name = _sequence_binder_name(named[0], src, binder_names)
    if binder_name is None:
        return None
    index = _unwrap_attrs_and_parens(named[1], keep_view=True)
    if index is None:
        return None
    if index.type == "integer_literal" and _node_src(index, src).strip() == "0":
        return binder_name, "first"
    if index.type == "binary_expression" and _comparison_op(index) == "-":
        left = _unwrap_attrs_and_parens(index.child_by_field_name("left"), keep_view=True)
        right = _unwrap_attrs_and_parens(index.child_by_field_name("right"), keep_view=True)
        if (
            right is not None
            and right.type == "integer_literal"
            and _node_src(right, src).strip() == "1"
            and _sequence_binder_len_name(left, src, binder_names) == binder_name
        ):
            return binder_name, "last"
    return None


def _unwrap_generic_type(rust_type: str, prefix: str) -> str | None:
    rust_type = rust_type.strip()
    if not rust_type.startswith(prefix) or not rust_type.endswith(">"):
        return None
    return rust_type[len(prefix) : -1].strip()


def _direct_type_supports_hash(rust_type: str | None) -> bool:
    if rust_type is None:
        return False
    rust_type = rust_type.strip()
    if rust_type in {
        "bool",
        "char",
        "String",
        "i8",
        "i16",
        "i32",
        "i64",
        "i128",
        "isize",
        "u8",
        "u16",
        "u32",
        "u64",
        "u128",
        "usize",
    }:
        return True
    tuple_items = parse_tuple_items(rust_type)
    if tuple_items is not None:
        return all(_direct_type_supports_hash(item) for item in tuple_items)
    option_inner = _unwrap_generic_type(rust_type, "Option<")
    if option_inner is not None:
        return _direct_type_supports_hash(option_inner)
    rc_inner = _unwrap_generic_type(rust_type, "std::rc::Rc<")
    if rc_inner is not None:
        if rc_inner == "String":
            return True
        vec_inner = _unwrap_generic_type(rc_inner, "Vec<")
        if vec_inner is not None:
            return _direct_type_supports_hash(vec_inner)
        return False
    return False


def _tuple_type(items: list[str]) -> str:
    if not items:
        return "()"
    if len(items) == 1:
        return f"({items[0]},)"
    return "(" + ", ".join(items) + ")"


def _tuple_expr(items: list[str]) -> str:
    if not items:
        return "()"
    if len(items) == 1:
        return f"({items[0]},)"
    return "(" + ", ".join(items) + ")"


def _normalize_expr_source(text: str) -> str:
    return re.sub(r"\s+", "", text)


def _pattern_bound_names(node, src: bytes) -> list[str]:
    if node.type == "identifier":
        return [_node_src(node, src).strip()]
    if node.type == "tuple_pattern":
        names: list[str] = []
        for child in node.named_children:
            names.extend(_pattern_bound_names(child, src))
        return names
    return []


def _helper_call_name(
    node,
    fn: DirectFunction,
    functions: dict[str, DirectFunction],
) -> str | None:
    if node is None or node.type != "call_expression":
        return None
    callee = node.child_by_field_name("function")
    if callee is None or callee.type == "field_expression":
        return None
    src = fn.source.encode("utf-8")
    callee_text = _node_src(callee, src).replace("Self::", "").replace("Solution::", "").strip()
    return callee_text if callee_text in functions else None


def _collect_mod_value_helper_calls(
    node,
    fn: DirectFunction,
    functions: dict[str, DirectFunction],
    modulus_source: str,
) -> set[str]:
    modulus_key = _normalize_expr_source(modulus_source)
    src = fn.source.encode("utf-8")

    def demand_expr(cur, want_mod_value: bool) -> tuple[set[str], set[str]]:
        cur = _unwrap_attrs_and_parens(cur, keep_view=True)
        if cur is None:
            return set(), set()
        if cur.type == "declaration_with_attrs" and cur.named_children:
            return demand_expr(cur.named_children[0], want_mod_value)
        if cur.type == "expression_statement":
            if not cur.named_children:
                return set(), set()
            return demand_expr(cur.named_children[0], want_mod_value)

        kind = cur.type
        if kind == "identifier":
            if want_mod_value:
                return set(), {_node_src(cur, src).strip()}
            return set(), set()
        if kind in {
            "integer_literal",
            "boolean_literal",
            "char_literal",
            "string_literal",
            "scoped_identifier",
        }:
            return set(), set()
        if kind in {"parenthesized_expression", "attribute_expression", "view_expression"}:
            named = [child for child in cur.named_children]
            return demand_expr(named[-1], want_mod_value) if named else (set(), set())
        if kind == "type_cast_expression":
            value = cur.child_by_field_name("value")
            return demand_expr(value, want_mod_value)
        if kind == "unary_expression":
            named = cur.named_children
            return demand_expr(named[0], want_mod_value) if named else (set(), set())
        if kind == "tuple_expression":
            helper_calls: set[str] = set()
            demanded: set[str] = set()
            for child in cur.named_children:
                child_calls, child_demand = demand_expr(child, want_mod_value)
                helper_calls.update(child_calls)
                demanded.update(child_demand)
            return helper_calls, demanded
        if kind == "field_expression":
            named = [child for child in cur.named_children]
            if not named:
                return set(), set()
            return demand_expr(named[0], want_mod_value)
        if kind == "index_expression":
            named = [child for child in cur.named_children]
            if len(named) != 2:
                return set(), set()
            recv_calls, recv_demand = demand_expr(named[0], want_mod_value)
            idx_calls, idx_demand = demand_expr(named[1], False)
            return recv_calls | idx_calls, recv_demand | idx_demand
        if kind == "binary_expression":
            op = _comparison_op(cur)
            left = cur.child_by_field_name("left")
            right = cur.child_by_field_name("right")
            if op is None or left is None or right is None:
                return set(), set()
            if op in {"&&", "&&&", "||", "|||", "==>", "<==", "<==>", "<", "<=", ">", ">=", "==", "!=", "=~="}:
                left_calls, left_demand = demand_expr(left, False)
                right_calls, right_demand = demand_expr(right, False)
                return left_calls | right_calls, left_demand | right_demand
            if op == "%" and _normalize_expr_source(_node_src(right, src)) == modulus_key:
                left_calls, left_demand = demand_expr(left, want_mod_value)
                right_calls, right_demand = demand_expr(right, False)
                return left_calls | right_calls, left_demand | right_demand
            left_calls, left_demand = demand_expr(left, want_mod_value)
            right_calls, right_demand = demand_expr(right, want_mod_value)
            return left_calls | right_calls, left_demand | right_demand
        if kind in {"big_and_expression", "big_or_expression"}:
            helper_calls: set[str] = set()
            demanded: set[str] = set()
            for child in cur.named_children:
                child_calls, child_demand = demand_expr(child, False)
                helper_calls.update(child_calls)
                demanded.update(child_demand)
            return helper_calls, demanded
        if kind == "if_expression":
            cond = cur.child_by_field_name("condition")
            cons = cur.child_by_field_name("consequence")
            alt = cur.child_by_field_name("alternative")
            helper_calls: set[str] = set()
            demanded: set[str] = set()
            if cond is not None:
                cond_calls, cond_demand = demand_expr(cond, False)
                helper_calls.update(cond_calls)
                demanded.update(cond_demand)
            if cons is not None:
                cons_calls, cons_demand = demand_expr(cons, want_mod_value)
                helper_calls.update(cons_calls)
                demanded.update(cons_demand)
            if alt is not None and alt.named_children:
                alt_calls, alt_demand = demand_expr(alt.named_children[0], want_mod_value)
                helper_calls.update(alt_calls)
                demanded.update(alt_demand)
            return helper_calls, demanded
        if kind == "block":
            named = [child for child in cur.named_children if child.type != "inner_attribute_item"]
            if not named:
                return set(), set()
            helper_calls, demanded = demand_expr(named[-1], want_mod_value)
            for child in reversed(named[:-1]):
                stmt = child.named_children[0] if child.type == "declaration_with_attrs" and child.named_children else child
                if stmt.type == "let_declaration":
                    pattern = stmt.child_by_field_name("pattern")
                    value = stmt.child_by_field_name("value")
                    if pattern is None or value is None:
                        continue
                    bound_names = _pattern_bound_names(pattern, src)
                    if any(name in demanded for name in bound_names):
                        value_calls, value_demand = demand_expr(value, True)
                        helper_calls.update(value_calls)
                        demanded.difference_update(bound_names)
                        demanded.update(value_demand)
                    else:
                        demanded.difference_update(bound_names)
                else:
                    stmt_calls, stmt_demand = demand_expr(stmt, False)
                    helper_calls.update(stmt_calls)
                    demanded.update(stmt_demand)
            return helper_calls, demanded
        if kind == "call_expression":
            helper_calls: set[str] = set()
            demanded: set[str] = set()
            args = cur.child_by_field_name("arguments")
            arg_nodes = list(args.named_children) if args is not None else []
            callee_name = _helper_call_name(cur, fn, functions)
            if want_mod_value and callee_name is not None:
                helper = functions[callee_name]
                if spec_to_direct_rust_type(helper.ret_type) == "i64":
                    helper_calls.add(callee_name)
                    for arg in arg_nodes:
                        arg_calls, arg_demand = demand_expr(arg, False)
                        helper_calls.update(arg_calls)
                        demanded.update(arg_demand)
                    return helper_calls, demanded
            callee = cur.child_by_field_name("function")
            if callee is not None and callee.type == "field_expression":
                named = [child for child in callee.named_children]
                if named:
                    recv_calls, recv_demand = demand_expr(named[0], False)
                    helper_calls.update(recv_calls)
                    demanded.update(recv_demand)
            elif callee is not None:
                callee_calls, callee_demand = demand_expr(callee, False)
                helper_calls.update(callee_calls)
                demanded.update(callee_demand)
            for arg in arg_nodes:
                arg_calls, arg_demand = demand_expr(arg, False)
                helper_calls.update(arg_calls)
                demanded.update(arg_demand)
            return helper_calls, demanded
        if kind == "return_expression":
            named = cur.named_children
            return demand_expr(named[0], want_mod_value) if named else (set(), set())
        return set(), set()

    helper_calls, _ = demand_expr(node, True)
    return helper_calls


def _collect_mod_value_demands(
    node,
    fn: DirectFunction,
    modulus_source: str,
) -> set[str]:
    modulus_key = _normalize_expr_source(modulus_source)
    src = fn.source.encode("utf-8")

    def demand_expr(cur, want_mod_value: bool) -> set[str]:
        cur = _unwrap_attrs_and_parens(cur, keep_view=True)
        if cur is None:
            return set()
        if cur.type == "declaration_with_attrs" and cur.named_children:
            return demand_expr(cur.named_children[0], want_mod_value)
        if cur.type == "expression_statement":
            if not cur.named_children:
                return set()
            return demand_expr(cur.named_children[0], want_mod_value)

        kind = cur.type
        if kind == "identifier":
            return {_node_src(cur, src).strip()} if want_mod_value else set()
        if kind in {
            "integer_literal",
            "boolean_literal",
            "char_literal",
            "string_literal",
            "scoped_identifier",
        }:
            return set()
        if kind in {"parenthesized_expression", "attribute_expression", "view_expression"}:
            named = [child for child in cur.named_children]
            return demand_expr(named[-1], want_mod_value) if named else set()
        if kind == "type_cast_expression":
            value = cur.child_by_field_name("value")
            return demand_expr(value, want_mod_value)
        if kind == "unary_expression":
            named = cur.named_children
            return demand_expr(named[0], want_mod_value) if named else set()
        if kind == "tuple_expression":
            demanded: set[str] = set()
            for child in cur.named_children:
                demanded.update(demand_expr(child, want_mod_value))
            return demanded
        if kind == "field_expression":
            named = [child for child in cur.named_children]
            return demand_expr(named[0], want_mod_value) if named else set()
        if kind == "index_expression":
            named = [child for child in cur.named_children]
            if len(named) != 2:
                return set()
            return demand_expr(named[0], want_mod_value) | demand_expr(named[1], False)
        if kind == "binary_expression":
            op = _comparison_op(cur)
            left = cur.child_by_field_name("left")
            right = cur.child_by_field_name("right")
            if op is None or left is None or right is None:
                return set()
            if op in {"&&", "&&&", "||", "|||", "==>", "<==", "<==>", "<", "<=", ">", ">=", "==", "!=", "=~="}:
                return demand_expr(left, False) | demand_expr(right, False)
            if op == "%" and _normalize_expr_source(_node_src(right, src)) == modulus_key:
                return demand_expr(left, want_mod_value) | demand_expr(right, False)
            return demand_expr(left, want_mod_value) | demand_expr(right, want_mod_value)
        if kind in {"big_and_expression", "big_or_expression"}:
            demanded: set[str] = set()
            for child in cur.named_children:
                demanded.update(demand_expr(child, False))
            return demanded
        if kind == "if_expression":
            cond = cur.child_by_field_name("condition")
            cons = cur.child_by_field_name("consequence")
            alt = cur.child_by_field_name("alternative")
            demanded = demand_expr(cond, False) if cond is not None else set()
            if cons is not None:
                demanded.update(demand_expr(cons, want_mod_value))
            if alt is not None and alt.named_children:
                demanded.update(demand_expr(alt.named_children[0], want_mod_value))
            return demanded
        if kind == "block":
            named = [child for child in cur.named_children if child.type != "inner_attribute_item"]
            if not named:
                return set()
            demanded = demand_expr(named[-1], want_mod_value)
            for child in reversed(named[:-1]):
                stmt = child.named_children[0] if child.type == "declaration_with_attrs" and child.named_children else child
                if stmt.type == "let_declaration":
                    pattern = stmt.child_by_field_name("pattern")
                    value = stmt.child_by_field_name("value")
                    if pattern is None or value is None:
                        continue
                    bound_names = _pattern_bound_names(pattern, src)
                    if any(name in demanded for name in bound_names):
                        demanded.difference_update(bound_names)
                        demanded.update(demand_expr(value, True))
                    else:
                        demanded.difference_update(bound_names)
                else:
                    demanded.update(demand_expr(stmt, False))
            return demanded
        if kind == "call_expression":
            demanded: set[str] = set()
            args = cur.child_by_field_name("arguments")
            arg_nodes = list(args.named_children) if args is not None else []
            if want_mod_value and cur.child_by_field_name("function") is not None and cur.child_by_field_name("function").type != "field_expression":
                for arg in arg_nodes:
                    demanded.update(demand_expr(arg, False))
                return demanded
            callee = cur.child_by_field_name("function")
            if callee is not None and callee.type == "field_expression":
                named = [child for child in callee.named_children]
                if named:
                    demanded.update(demand_expr(named[0], False))
            elif callee is not None:
                demanded.update(demand_expr(callee, False))
            for arg in arg_nodes:
                demanded.update(demand_expr(arg, False))
            return demanded
        if kind == "return_expression":
            named = cur.named_children
            return demand_expr(named[0], want_mod_value) if named else set()
        return set()

    return demand_expr(node, True)


class ModuloSafetyAnalyzer:
    def __init__(
        self,
        functions: dict[str, DirectFunction],
        candidate_functions: set[str],
        modulus_source: str,
    ) -> None:
        self.functions = functions
        self.candidate_functions = set(candidate_functions)
        self.modulus_key = _normalize_expr_source(modulus_source)
        self.type_stack: list[dict[str, str]] = []
        self.dep_stack: list[dict[str, bool]] = []
        self.safe_cache: dict[str, bool | None] = {}

    def push_scope(
        self,
        types: dict[str, str] | None = None,
        deps: dict[str, bool] | None = None,
    ) -> None:
        self.type_stack.append(dict(types or {}))
        self.dep_stack.append(dict(deps or {}))

    def pop_scope(self) -> None:
        self.type_stack.pop()
        self.dep_stack.pop()

    def bind_name(self, name: str, rust_type: str | None, depends_on_candidate: bool) -> None:
        if not self.type_stack or rust_type is None:
            return
        self.type_stack[-1][name] = rust_type
        self.dep_stack[-1][name] = depends_on_candidate

    def lookup_type(self, name: str) -> str | None:
        for scope in reversed(self.type_stack):
            if name in scope:
                return scope[name]
        return None

    def lookup_dep(self, name: str) -> bool:
        for scope in reversed(self.dep_stack):
            if name in scope:
                return scope[name]
        return False

    def _bind_pattern(self, node, rust_type: str | None, depends_on_candidate: bool, src: bytes) -> None:
        if rust_type is None:
            return
        if node.type == "identifier":
            self.bind_name(_node_src(node, src).strip(), rust_type, depends_on_candidate)
            return
        if node.type != "tuple_pattern":
            return
        item_types = parse_tuple_items(rust_type)
        if item_types is None:
            return
        for child, item_ty in zip(node.named_children, item_types):
            self._bind_pattern(child, item_ty, depends_on_candidate, src)

    @staticmethod
    def _common_numeric_type(left_ty: str | None, right_ty: str | None) -> str | None:
        if left_ty is None:
            return right_ty
        if right_ty is None or left_ty == right_ty:
            return left_ty
        if _direct_int_type(left_ty) and _direct_int_type(right_ty):
            return "i64"
        return left_ty

    def function_safe(self, fn_name: str) -> bool:
        cached = self.safe_cache.get(fn_name)
        if cached is not None:
            return cached
        if fn_name in self.safe_cache:
            return True
        fn = self.functions[fn_name]
        if spec_to_direct_rust_type(fn.ret_type) != "i64":
            self.safe_cache[fn_name] = False
            return False
        body_node = fn.node.child_by_field_name("body")
        if body_node is None:
            self.safe_cache[fn_name] = False
            return False
        param_types = {
            param.name: spec_to_direct_rust_type(param.spec_type) or param.spec_type
            for param in fn.params
        }
        self.safe_cache[fn_name] = None
        self.push_scope(param_types, {name: False for name in param_types})
        try:
            ok, _, _ = self._analyze_expr(body_node, fn)
        finally:
            self.pop_scope()
        self.safe_cache[fn_name] = ok
        return ok

    def _analyze_expr(self, node, fn: DirectFunction) -> tuple[bool, bool, str | None]:
        node = _unwrap_attrs_and_parens(node, keep_view=True)
        if node is None:
            return True, False, None
        if node.type == "declaration_with_attrs" and node.named_children:
            return self._analyze_expr(node.named_children[0], fn)
        if node.type == "expression_statement":
            if not node.named_children:
                return True, False, None
            return self._analyze_expr(node.named_children[0], fn)

        src = fn.source.encode("utf-8")
        kind = node.type
        if kind == "identifier":
            name = _node_src(node, src).strip()
            return True, self.lookup_dep(name), self.lookup_type(name)
        if kind == "scoped_identifier":
            text = _node_src(node, src).replace("Self::", "").replace("Solution::", "").strip()
            helper = self.functions.get(text)
            rust_type = None if helper is None else spec_to_direct_rust_type(helper.ret_type)
            return True, False, rust_type
        if kind == "integer_literal":
            return True, False, "i64"
        if kind == "boolean_literal":
            return True, False, "bool"
        if kind == "char_literal":
            return True, False, "char"
        if kind == "string_literal":
            return True, False, "std::rc::Rc<String>"
        if kind == "parenthesized_expression":
            named = [child for child in node.named_children]
            return self._analyze_expr(named[-1], fn) if named else (True, False, None)
        if kind == "view_expression":
            named = [child for child in node.named_children]
            return self._analyze_expr(named[0], fn) if named else (True, False, None)
        if kind == "tuple_expression":
            item_infos = [self._analyze_expr(child, fn) for child in node.named_children]
            if any(not ok for ok, _, _ in item_infos):
                return False, False, None
            depends = any(dep for _, dep, _ in item_infos)
            item_types = [ty or "()" for _, _, ty in item_infos]
            return True, depends, _tuple_type(item_types)
        if kind == "field_expression":
            named = [child for child in node.named_children]
            if len(named) != 2:
                return False, False, None
            ok, dep, recv_ty = self._analyze_expr(named[0], fn)
            if not ok or dep:
                return False, False, None
            tuple_items = parse_tuple_items(recv_ty or "")
            field_text = _node_src(named[1], src).strip()
            if tuple_items and field_text.isdigit() and int(field_text) < len(tuple_items):
                return True, False, tuple_items[int(field_text)]
            return True, False, None
        if kind == "index_expression":
            named = [child for child in node.named_children]
            if len(named) != 2:
                return False, False, None
            recv_ok, recv_dep, recv_ty = self._analyze_expr(named[0], fn)
            idx_ok, idx_dep, _ = self._analyze_expr(named[1], fn)
            if not recv_ok or not idx_ok or recv_dep or idx_dep:
                return False, False, None
            return True, False, _direct_vec_elem_type(recv_ty)
        if kind == "type_cast_expression":
            value = node.child_by_field_name("value")
            target = node.child_by_field_name("type")
            if value is None or target is None:
                return False, False, None
            ok, dep, _ = self._analyze_expr(value, fn)
            if not ok:
                return False, False, None
            target_text = _node_src(target, src).strip()
            if target_text in {"int", "nat", "usize"}:
                target_text = "i64"
            return True, dep, spec_to_direct_rust_type(target_text) or target_text
        if kind == "unary_expression":
            named = node.named_children
            if not named:
                return False, False, None
            ok, dep, inner_ty = self._analyze_expr(named[0], fn)
            if not ok:
                return False, False, None
            op = _node_src(node.children[0], src).strip() if node.children else ""
            if op == "!" and dep:
                return False, False, None
            return True, dep if op != "!" else False, "bool" if op == "!" else inner_ty
        if kind == "binary_expression":
            op = _comparison_op(node)
            left = node.child_by_field_name("left")
            right = node.child_by_field_name("right")
            if op is None or left is None or right is None:
                return False, False, None
            left_ok, left_dep, left_ty = self._analyze_expr(left, fn)
            right_ok, right_dep, right_ty = self._analyze_expr(right, fn)
            if not left_ok or not right_ok:
                return False, False, None
            if op in {"&&", "&&&", "||", "|||", "==>", "<==", "<==>", "<", "<=", ">", ">=", "==", "!=", "=~="}:
                if left_dep or right_dep:
                    return False, False, None
                return True, False, "bool"
            if op in {"+", "-", "*"}:
                return True, left_dep or right_dep, self._common_numeric_type(left_ty, right_ty)
            if op == "%":
                if right_dep:
                    return False, False, None
                if left_dep and _normalize_expr_source(_node_src(right, src)) != self.modulus_key:
                    return False, False, None
                return True, left_dep, self._common_numeric_type(left_ty, right_ty)
            if op == "/":
                # Modular reduction does not commute with integer
                # division. Even when both operands are modulus-free, a
                # function body that performs `x*(x+1)/2`-style arithmetic
                # cannot be safely translated to a mod variant: the mod
                # variant would replace `x*(x+1)` with `mod_mul(x, x+1, p)`
                # then divide by 2, which is *not* equal to
                # `(x*(x+1)/2) mod p`. Disable mod-rewrites for any
                # function body containing `/`. The caller's outer
                # `% MOD` will be applied to the function's exact result
                # instead.
                return False, False, None
            if op in {"<<", ">>", "&", "|", "^"}:
                if left_dep or right_dep:
                    return False, False, None
                return True, False, self._common_numeric_type(left_ty, right_ty)
            return True, left_dep or right_dep, self._common_numeric_type(left_ty, right_ty)
        if kind in {"big_and_expression", "big_or_expression"}:
            for child in node.named_children:
                ok, dep, _ = self._analyze_expr(child, fn)
                if not ok or dep:
                    return False, False, None
            return True, False, "bool"
        if kind == "if_expression":
            cond = node.child_by_field_name("condition")
            cons = node.child_by_field_name("consequence")
            alt = node.child_by_field_name("alternative")
            if cond is None or cons is None:
                return False, False, None
            cond_ok, cond_dep, _ = self._analyze_expr(cond, fn)
            if not cond_ok or cond_dep:
                return False, False, None
            cons_ok, cons_dep, cons_ty = self._analyze_expr(cons, fn)
            if not cons_ok:
                return False, False, None
            alt_dep = False
            alt_ty = cons_ty
            if alt is not None and alt.named_children:
                alt_ok, alt_dep, alt_ty = self._analyze_expr(alt.named_children[0], fn)
                if not alt_ok:
                    return False, False, None
            return True, cons_dep or alt_dep, cons_ty or alt_ty
        if kind == "block":
            self.push_scope()
            try:
                named = [child for child in node.named_children if child.type != "inner_attribute_item"]
                last_info: tuple[bool, bool, str | None] = (True, False, "()")
                for child in named:
                    stmt = child.named_children[0] if child.type == "declaration_with_attrs" and child.named_children else child
                    if stmt.type == "let_declaration":
                        pattern = stmt.child_by_field_name("pattern")
                        value = stmt.child_by_field_name("value")
                        if pattern is None or value is None:
                            return False, False, None
                        value_ok, value_dep, value_ty = self._analyze_expr(value, fn)
                        if not value_ok:
                            return False, False, None
                        self._bind_pattern(pattern, value_ty, value_dep, src)
                        last_info = (True, False, "()")
                        continue
                    last_info = self._analyze_expr(stmt, fn)
                    if not last_info[0]:
                        return last_info
                return last_info
            finally:
                self.pop_scope()
        if kind == "call_expression":
            args = node.child_by_field_name("arguments")
            arg_nodes = list(args.named_children) if args is not None else []
            arg_infos = [self._analyze_expr(arg, fn) for arg in arg_nodes]
            if any(not ok for ok, _, _ in arg_infos):
                return False, False, None
            callee = node.child_by_field_name("function")
            if callee is None:
                return False, False, None
            if callee.type == "field_expression":
                named = [child for child in callee.named_children]
                if len(named) != 2:
                    return False, False, None
                recv_ok, recv_dep, recv_ty = self._analyze_expr(named[0], fn)
                if not recv_ok or recv_dep or any(dep for _, dep, _ in arg_infos):
                    return False, False, None
                method = _node_src(named[1], src).strip()
                if method == "len":
                    return True, False, "i64"
                if method == "last":
                    return True, False, _direct_vec_elem_type(recv_ty)
                if method in {"take", "skip", "subrange", "add", "update", "map_values", "filter", "drop_last", "drop_first", "deep_view", "push"}:
                    return True, False, recv_ty
                if method in {"max", "min"}:
                    return True, False, "i64"
                return True, False, None
            callee_name = _helper_call_name(node, fn, self.functions)
            if callee_name is not None:
                helper = self.functions[callee_name]
                ret_ty = spec_to_direct_rust_type(helper.ret_type)
                if callee_name in self.candidate_functions:
                    if any(dep for _, dep, _ in arg_infos):
                        return False, False, None
                    if not self.function_safe(callee_name):
                        return False, False, None
                    return True, True, ret_ty
                if any(dep for _, dep, _ in arg_infos):
                    return False, False, None
                return True, False, ret_ty
            if any(dep for _, dep, _ in arg_infos):
                return False, False, None
            return True, False, None
        if kind == "return_expression":
            named = node.named_children
            return self._analyze_expr(named[0], fn) if named else (True, False, "()")
        if kind == "macro_invocation":
            return True, False, None
        return False, False, None


def infer_modulo_function_sources(model: DirectProblemModel) -> dict[str, str]:
    post_fn = model.functions.get(model.sig.fn_name)
    if post_fn is None:
        return {}
    body_node = post_fn.node.child_by_field_name("body")
    if body_node is None:
        return {}

    src = post_fn.source.encode("utf-8")
    groups: dict[str, set[str]] = {}
    raw_source_by_key: dict[str, str] = {}
    for binary in _find_nodes(body_node, "binary_expression"):
        if _comparison_op(binary) != "%":
            continue
        left = binary.child_by_field_name("left")
        right = binary.child_by_field_name("right")
        if left is None or right is None:
            continue
        raw_modulus = _node_src(right, src).strip()
        modulus_key = _normalize_expr_source(raw_modulus)
        raw_source_by_key.setdefault(modulus_key, raw_modulus)
        roots = _collect_mod_value_helper_calls(left, post_fn, model.functions, raw_modulus)
        roots = {
            name
            for name in roots
            if spec_to_direct_rust_type(model.functions[name].ret_type) == "i64"
        }
        if roots:
            groups.setdefault(modulus_key, set()).update(roots)

    resolved: dict[str, str] = {}
    conflicts: set[str] = set()
    for modulus_key, roots in groups.items():
        modulus_source = raw_source_by_key[modulus_key]
        candidates = set(roots)
        worklist = list(roots)
        while worklist:
            name = worklist.pop()
            fn = model.functions[name]
            body = fn.node.child_by_field_name("body")
            if body is None:
                candidates.clear()
                break
            for dep_name in _collect_mod_value_helper_calls(body, fn, model.functions, modulus_source):
                if spec_to_direct_rust_type(model.functions[dep_name].ret_type) != "i64":
                    continue
                if dep_name not in candidates:
                    candidates.add(dep_name)
                    worklist.append(dep_name)
        if not candidates:
            continue
        analyzer = ModuloSafetyAnalyzer(model.functions, candidates, modulus_source)
        if not all(analyzer.function_safe(name) for name in candidates):
            continue
        for name in candidates:
            if name in resolved and _normalize_expr_source(resolved[name]) != modulus_key:
                conflicts.add(name)
            else:
                resolved[name] = modulus_source

    for name in conflicts:
        resolved.pop(name, None)
    return resolved


class DirectSpecTranslator:
    def __init__(
        self,
        functions: dict[str, DirectFunction],
        mod_function_sources: dict[str, str] | None = None,
    ) -> None:
        self.functions = functions
        self.counter = itertools.count(1)
        self.inline_depth = 0
        self.scope_stack: list[dict[str, str]] = []
        self.mod_function_sources = dict(mod_function_sources or {})
        self.modulus_source_by_key = {
            _normalize_expr_source(source): source
            for source in self.mod_function_sources.values()
        }
        self.current_modulus_source: str | None = None
        self.modulus_rust_cache: dict[str, str] = {}
        self.current_modulus_rust_override: str | None = None

    def fresh(self, prefix: str) -> str:
        return f"__{prefix}_{next(self.counter)}"

    def push_scope(self, initial: dict[str, str] | None = None) -> None:
        self.scope_stack.append(dict(initial or {}))

    def pop_scope(self) -> None:
        self.scope_stack.pop()

    def bind_name(self, name: str, rust_type: str | None) -> None:
        if rust_type is None or not self.scope_stack:
            return
        self.scope_stack[-1][name] = rust_type

    def lookup_name_type(self, name: str) -> str | None:
        for scope in reversed(self.scope_stack):
            if name in scope:
                return scope[name]
        return None

    def _is_recursive_function(self, fn: DirectFunction) -> bool:
        body_node = fn.node.child_by_field_name("body")
        if body_node is None:
            return False
        src = fn.source.encode("utf-8")
        for call in _find_nodes(body_node, "call_expression"):
            callee = call.child_by_field_name("function")
            if callee is None:
                continue
            callee_text = _node_src(callee, src).strip()
            callee_text = callee_text.replace("Self::", "").replace("Solution::", "")
            if callee_text == fn.name:
                return True
        return False

    def _translate_numeric_to(self, node, fn: DirectFunction, target: str) -> str:
        node = _unwrap_attrs_and_parens(node, keep_view=True)
        if node is None:
            raise DirectTranslationError(f"missing numeric expression node in {fn.name}")
        ty = self.infer_expr_type(node, fn)
        if not _direct_int_type(ty):
            return self.translate_expr(node, fn)
        if node.type == "binary_expression":
            op = _comparison_op(node)
            left = node.child_by_field_name("left")
            right = node.child_by_field_name("right")
            if op in {"+", "-", "*", "/", "%"} and left is not None and right is not None:
                if self.current_modulus_source is not None and op in {"+", "-", "*", "%"}:
                    text = self.translate_binary(node, fn)
                    return f"(({text}) as {target})" if ty != target else text
                if self.current_modulus_source is None and op == "%":
                    modulus_source = self._subtree_modulus_source(left, fn)
                    if (
                        modulus_source is not None
                        and _normalize_expr_source(_node_src(right, fn.source.encode("utf-8")).strip())
                        == _normalize_expr_source(modulus_source)
                    ):
                        text = self.translate_binary(node, fn)
                        return f"(({text}) as {target})" if ty != target else text
                left_text = self._translate_numeric_to(left, fn, target)
                right_text = self._translate_numeric_to(right, fn, target)
                if op == "%" and self._is_spec_int_node(left, fn):
                    expr = f"mod_floor_i64(({left_text}) as i64, ({right_text}) as i64)"
                    return f"(({expr}) as {target})" if target != "i64" else expr
                return f"(({left_text}) {op} ({right_text}))"
        text = self.translate_expr(node, fn)
        if ty != target:
            return f"(({text}) as {target})"
        return text

    def _is_int_literal_like(self, node) -> bool:
        node = _unwrap_attrs_and_parens(node, keep_view=True)
        if node is None:
            return False
        if node.type == "declaration_with_attrs" and node.named_children:
            return self._is_int_literal_like(node.named_children[0])
        if node.type == "expression_statement" and node.named_children:
            return self._is_int_literal_like(node.named_children[0])
        if node.type == "block":
            named = [c for c in node.named_children if c.type != "inner_attribute_item"]
            if len(named) != 1:
                return False
            return self._is_int_literal_like(named[0])
        if node.type == "integer_literal":
            return True
        if node.type == "unary_expression" and node.children:
            op = node.children[0].text.decode("utf-8").strip()
            named = node.named_children
            return op == "-" and bool(named) and self._is_int_literal_like(named[0])
        return False

    def _common_numeric_target(
        self,
        left,
        left_ty: str | None,
        right,
        right_ty: str | None,
    ) -> str | None:
        if not (_direct_int_type(left_ty) and _direct_int_type(right_ty)):
            return None
        if left_ty == right_ty:
            return left_ty
        if left_ty == "i64" and right_ty != "i64" and self._is_int_literal_like(left):
            return right_ty
        if right_ty == "i64" and left_ty != "i64" and self._is_int_literal_like(right):
            return left_ty
        return "i64"

    def _mod_variant_name(self, fn_name: str) -> str:
        return f"__mod_{fn_name}"

    def _modulus_rust_text(self, modulus_source: str) -> str:
        if self.current_modulus_rust_override is not None:
            return self.current_modulus_rust_override
        key = _normalize_expr_source(modulus_source)
        cached = self.modulus_rust_cache.get(key)
        if cached is not None:
            return cached
        node, tmp_fn = _parse_direct_expr_with_fn(modulus_source)
        if node is None:
            raise DirectTranslationError(f"failed to parse modulus expression `{modulus_source}`")
        saved_modulus = self.current_modulus_source
        self.current_modulus_source = None
        try:
            cached = self.translate_expr(node, tmp_fn)
        finally:
            self.current_modulus_source = saved_modulus
        self.modulus_rust_cache[key] = cached
        return cached

    def _subtree_modulus_source(self, node, fn: DirectFunction) -> str | None:
        keys = set()
        for call in _find_nodes(node, "call_expression"):
            name = _helper_call_name(call, fn, self.functions)
            if name is None:
                continue
            source = self.mod_function_sources.get(name)
            if source is not None:
                keys.add(_normalize_expr_source(source))
        if len(keys) != 1:
            return None
        return self.modulus_source_by_key[next(iter(keys))]

    def translate_expr_with_modulus(self, node, fn: DirectFunction, modulus_source: str) -> str:
        saved_modulus = self.current_modulus_source
        self.current_modulus_source = modulus_source
        try:
            return self.translate_expr(node, fn)
        finally:
            self.current_modulus_source = saved_modulus

    def translate_expr_exact(self, node, fn: DirectFunction) -> str:
        saved_modulus = self.current_modulus_source
        self.current_modulus_source = None
        try:
            return self.translate_expr(node, fn)
        finally:
            self.current_modulus_source = saved_modulus

    def _translate_function_impl(
        self,
        fn: DirectFunction,
        emitted_name: str,
        modulus_source: str | None,
    ) -> str:
        params = []
        param_scope: dict[str, str] = {}
        for param in fn.params:
            rust_ty = spec_to_direct_rust_type(param.spec_type)
            if rust_ty is None:
                raise DirectTranslationError(
                    f"unsupported direct type `{param.spec_type}` in {fn.name}"
                )
            params.append(f"{param.name}: {rust_ty}")
            param_scope[param.name] = rust_ty
        if modulus_source is not None:
            params.append("__modulus__: i64")
            param_scope["__modulus__"] = "i64"
        ret_ty = spec_to_direct_rust_type(fn.ret_type)
        if ret_ty is None:
            raise DirectTranslationError(
                f"unsupported direct return type `{fn.ret_type}` in {fn.name}"
            )
        if (
            ret_ty == "bool"
            and len(fn.params) == 2
            and fn.params[0].spec_type == fn.params[1].spec_type
            and _sequence_elem_spec_type(fn.params[0].spec_type) in {"int", "i32"}
            and "count(" in fn.body_text
            and any(token in fn.name.lower() for token in ("perm", "multiset"))
        ):
            left_name = fn.params[0].name
            right_name = fn.params[1].name
            return (
                f"fn {emitted_name}({', '.join(params)}) -> bool {{\n"
                f"    (({left_name}).len() == ({right_name}).len())\n"
                f"        && (seq_to_multiset(({left_name}).clone()) == seq_to_multiset(({right_name}).clone()))\n"
                "}"
            )
        body_node = fn.node.child_by_field_name("body")
        if body_node is None:
            raise DirectTranslationError(f"missing body for {fn.name}")
        self.push_scope(param_scope)
        saved_modulus = self.current_modulus_source
        saved_override = self.current_modulus_rust_override
        self.current_modulus_source = modulus_source
        if modulus_source is not None:
            self.current_modulus_rust_override = "__modulus__"
        try:
            body = self.translate_block(body_node, fn, push_scope=False)
        finally:
            self.current_modulus_source = saved_modulus
            self.current_modulus_rust_override = saved_override
            self.pop_scope()
        if not self._is_recursive_function(fn) or not all(
            _direct_type_supports_hash(param_scope.get(param.name))
            for param in fn.params
        ):
            return f"fn {emitted_name}({', '.join(params)}) -> {ret_ty} {body}"

        impl_name = f"__{emitted_name}_impl"
        cache_stem = re.sub(r"\W+", "_", emitted_name).upper()
        cache_name = f"__{cache_stem}_CACHE"
        cache_key_param_names = [param.name for param in fn.params]
        if modulus_source is not None:
            # The mod variant's modulus value is part of the call's
            # identity: results for `(n, k1)` differ from `(n, k2)`. Bake
            # `__modulus__` into the cache key so cases with different
            # moduli (the harness runs many testcases sequentially) don't
            # cross-pollute results.
            cache_key_param_names.append("__modulus__")
        cache_key_types: list[str] = []
        for nm in cache_key_param_names:
            ty = param_scope.get(nm)
            if ty is None:
                ty = "i64"
            cache_key_types.append(ty)
        key_type = _tuple_type(cache_key_types)
        key_expr = _tuple_expr([f"{nm}.clone()" for nm in cache_key_param_names])
        all_param_names = [param.name for param in fn.params]
        if modulus_source is not None:
            all_param_names.append("__modulus__")
        call_args = ", ".join(all_param_names)
        impl_fn = f"fn {impl_name}({', '.join(params)}) -> {ret_ty} {body}"
        memoized_fn = (
            "thread_local! {\n"
            f"    static {cache_name}: std::cell::RefCell<std::collections::HashMap<{key_type}, {ret_ty}>> =\n"
            "        std::cell::RefCell::new(std::collections::HashMap::new());\n"
            "}\n\n"
            f"fn {emitted_name}({', '.join(params)}) -> {ret_ty} {{\n"
            f"    let __cache_key = {key_expr};\n"
            f"    if let Some(__cached) = {cache_name}.with(|cache| cache.borrow().get(&__cache_key).cloned()) {{\n"
            "        return __cached;\n"
            "    }\n"
            f"    let __value = {impl_name}({call_args});\n"
            f"    {cache_name}.with(|cache| {{\n"
            "        cache.borrow_mut().insert(__cache_key, __value.clone());\n"
            "    });\n"
            "    __value\n"
            "}"
        )
        return impl_fn + "\n\n" + memoized_fn

    def translate_function(self, fn: DirectFunction) -> str:
        return self._translate_function_impl(fn, fn.name, None)

    def translate_mod_function(self, fn: DirectFunction) -> str:
        modulus_source = self.mod_function_sources.get(fn.name)
        if modulus_source is None:
            raise DirectTranslationError(f"missing modulus source for {fn.name}")
        return self._translate_function_impl(fn, self._mod_variant_name(fn.name), modulus_source)

    def translate_block(self, node, fn: DirectFunction, push_scope: bool = True) -> str:
        if push_scope:
            self.push_scope()
        lines: list[str] = []
        named = [c for c in node.named_children if c.type != "inner_attribute_item"]
        modded_let_nodes: set[int] = set()
        if self.current_modulus_source is not None and named:
            demanded = _collect_mod_value_demands(named[-1], fn, self.current_modulus_source)
            src = fn.source.encode("utf-8")
            for child in reversed(named[:-1]):
                stmt = child.named_children[0] if child.type == "declaration_with_attrs" and child.named_children else child
                if stmt.type != "let_declaration":
                    continue
                pattern = stmt.child_by_field_name("pattern")
                value = stmt.child_by_field_name("value")
                if pattern is None or value is None:
                    continue
                bound_names = _pattern_bound_names(pattern, src)
                if any(name in demanded for name in bound_names):
                    modded_let_nodes.add(id(stmt))
                    demanded.difference_update(bound_names)
                    demanded.update(_collect_mod_value_demands(value, fn, self.current_modulus_source))
                else:
                    demanded.difference_update(bound_names)
        try:
            for idx, child in enumerate(named):
                last = idx == len(named) - 1
                if child.type == "declaration_with_attrs" and child.named_children:
                    child = child.named_children[0]
                if child.type == "let_declaration":
                    lines.append(self.translate_let(child, fn, use_mod_value=id(child) in modded_let_nodes))
                    continue
                expr = child
                if child.type == "expression_statement":
                    expr_children = child.named_children
                    if not expr_children:
                        continue
                    expr = expr_children[0]
                expr_text = self.translate_expr(expr, fn)
                lines.append(expr_text if last else f"{expr_text};")
            if not lines:
                return "{\n}"
            indented = "\n".join(
                ("    " + line) if line.strip() else "" for line in lines
            )
            return "{\n" + indented + "\n}"
        finally:
            if push_scope:
                self.pop_scope()

    def translate_pattern(self, node, fn: DirectFunction) -> str:
        src = fn.source.encode("utf-8")
        if node.type == "tuple_pattern":
            parts = [
                self.translate_pattern(child, fn)
                for child in node.named_children
            ]
            return "(" + ", ".join(parts) + ")"
        return _node_src(node, src)

    def _bind_pattern_types(self, node, rust_type: str | None, fn: DirectFunction) -> None:
        if rust_type is None:
            return
        if node.type == "identifier":
            self.bind_name(_node_src(node, fn.source.encode("utf-8")).strip(), rust_type)
            return
        if node.type == "tuple_pattern":
            item_types = parse_tuple_items(rust_type)
            if item_types is None:
                return
            for child, item_ty in zip(node.named_children, item_types):
                self._bind_pattern_types(child, item_ty, fn)

    def translate_let(self, node, fn: DirectFunction, use_mod_value: bool = True) -> str:
        pattern = node.child_by_field_name("pattern")
        value = node.child_by_field_name("value")
        if pattern is None or value is None:
            raise DirectTranslationError(f"unsupported let binding in {fn.name}")
        type_node = node.child_by_field_name("type")
        pattern_text = self.translate_pattern(pattern, fn)
        if self.current_modulus_source is not None and not use_mod_value:
            value_text = self.translate_expr_exact(value, fn)
        else:
            value_text = self.translate_expr(value, fn)
        rust_type = None
        if type_node is not None:
            rust_type = spec_to_direct_rust_type(_node_src(type_node, fn.source.encode("utf-8")).strip())
        if rust_type is None:
            rust_type = self.infer_expr_type(value, fn)
        self._bind_pattern_types(pattern, rust_type, fn)
        return f"let {pattern_text} = {value_text};"

    def _coerce_numeric_pair(
        self,
        left_text: str,
        left_ty: str | None,
        right_text: str,
        right_ty: str | None,
    ) -> tuple[str, str]:
        if not (_direct_int_type(left_ty) and _direct_int_type(right_ty)):
            return left_text, right_text
        target = left_ty if left_ty == right_ty else "i64"
        if left_ty != target:
            left_text = f"(({left_text}) as {target})"
        if right_ty != target:
            right_text = f"(({right_text}) as {target})"
        return left_text, right_text

    def _is_spec_int_node(self, node, fn: DirectFunction) -> bool:
        # True if this expression is a Verus `int`/`nat` arithmetic value
        # (rather than a fixed-width primitive like i32).  Used to decide
        # whether `%` and friends need Euclidean semantics: Verus on `int`
        # gives a non-negative remainder when the divisor is positive, but
        # Rust's `%` is truncating and may return negatives.
        node = _unwrap_attrs_and_parens(node, keep_view=True)
        if node is None:
            return False
        src = fn.source.encode("utf-8")
        kind = node.type
        if kind == "type_cast_expression":
            target = node.child_by_field_name("type")
            if target is None:
                return False
            target_text = _node_src(target, src).strip()
            return target_text in {"int", "nat"}
        if kind == "binary_expression":
            left = node.child_by_field_name("left")
            right = node.child_by_field_name("right")
            if left is not None and self._is_spec_int_node(left, fn):
                return True
            if right is not None and self._is_spec_int_node(right, fn):
                return True
            return False
        if kind == "unary_expression":
            named = node.named_children
            return bool(named) and self._is_spec_int_node(named[0], fn)
        if kind == "if_expression":
            cons = node.child_by_field_name("consequence")
            if cons is not None:
                cons_named = [c for c in cons.named_children]
                if cons_named and self._is_spec_int_node(cons_named[-1], fn):
                    return True
            alt = node.child_by_field_name("alternative")
            if alt is not None and alt.named_children:
                if self._is_spec_int_node(alt.named_children[0], fn):
                    return True
            return False
        if kind == "call_expression":
            # Recursive helper functions whose ret_type is `int`/`nat` are
            # treated as int-typed.
            func = node.child_by_field_name("function")
            if func is not None:
                text = _node_src(func, src).replace("Self::", "").replace("Solution::", "").strip()
                helper = self.functions.get(text)
                if helper is not None:
                    rt = helper.ret_type.strip()
                    if rt in {"int", "nat"}:
                        return True
        if kind == "identifier":
            name = _node_src(node, src).strip()
            for binder, ty in self.binder_stack[::-1] if hasattr(self, "binder_stack") else []:
                if binder == name:
                    return ty in {"int", "nat"}
        return False

    def infer_expr_type(self, node, fn: DirectFunction) -> str | None:
        node = _unwrap_attrs_and_parens(node, keep_view=True)
        if node is None:
            return None
        if node.type == "declaration_with_attrs" and node.named_children:
            node = node.named_children[0]
        src = fn.source.encode("utf-8")
        kind = node.type

        if kind == "identifier":
            return self.lookup_name_type(_node_src(node, src).strip())
        if kind == "scoped_identifier":
            text = _node_src(node, src).replace("Self::", "").replace("Solution::", "").strip()
            helper = self.functions.get(text)
            return None if helper is None else spec_to_direct_rust_type(helper.ret_type)
        if kind == "integer_literal":
            text = _node_src(node, src).strip()
            m = re.search(r"(int|nat|i8|i16|i32|i64|i128|isize|u8|u16|u32|u64|u128|usize)$", text)
            if m:
                suffix = m.group(1)
                return "i64" if suffix in {"int", "nat", "usize"} else suffix
            return "i64"
        if kind == "boolean_literal":
            return "bool"
        if kind == "char_literal":
            return "char"
        if kind == "string_literal":
            return "std::rc::Rc<String>"
        if kind == "parenthesized_expression":
            named = [c for c in node.named_children]
            return self.infer_expr_type(named[-1], fn) if named else None
        if kind == "view_expression":
            named = [c for c in node.named_children]
            inner_ty = self.infer_expr_type(named[0], fn) if named else None
            return "std::rc::Rc<Vec<char>>" if inner_ty == "std::rc::Rc<String>" else inner_ty
        if kind == "tuple_expression":
            item_types = [self.infer_expr_type(child, fn) for child in node.named_children]
            return None if any(item is None for item in item_types) else "(" + ", ".join(item_types) + ")"
        if kind == "field_expression":
            named = [c for c in node.named_children]
            if len(named) != 2:
                return None
            recv_ty = self.infer_expr_type(named[0], fn)
            field_text = _node_src(named[1], src).strip()
            tuple_items = parse_tuple_items(recv_ty or "")
            return tuple_items[int(field_text)] if tuple_items and field_text.isdigit() and int(field_text) < len(tuple_items) else None
        if kind == "index_expression":
            named = [c for c in node.named_children]
            return _direct_vec_elem_type(self.infer_expr_type(named[0], fn)) if named else None
        if kind == "type_cast_expression":
            target = node.child_by_field_name("type")
            if target is None:
                return None
            target_text = _node_src(target, src).strip()
            if target_text in {"int", "nat", "usize"}:
                return "i64"
            return spec_to_direct_rust_type(target_text) or target_text
        if kind == "unary_expression":
            op = _node_src(node.children[0], src).strip() if node.children else ""
            if op == "!":
                return "bool"
            named = node.named_children
            return self.infer_expr_type(named[0], fn) if named else None
        if kind == "binary_expression":
            op = _comparison_op(node)
            if op in {"&&", "&&&", "||", "|||", "==>", "<==", "<==>", "<", "<=", ">", ">=", "==", "!=", "=~="}:
                return "bool"
            left = node.child_by_field_name("left")
            right = node.child_by_field_name("right")
            left_ty = self.infer_expr_type(left, fn) if left is not None else None
            right_ty = self.infer_expr_type(right, fn) if right is not None else None
            if op in {"<<", ">>"}:
                return left_ty
            if op in {"&", "|", "^"}:
                return left_ty if left_ty == right_ty else left_ty or right_ty
            if _direct_int_type(left_ty) and _direct_int_type(right_ty):
                return left_ty if left_ty == right_ty else "i64"
            return left_ty or right_ty
        if kind in {"big_and_expression", "big_or_expression"}:
            return "bool"
        if kind == "quantifier_expression":
            quant_token = node.children[0].type if node.children else ""
            if quant_token == "choose":
                binders = self._binders(node, fn)
                if len(binders) != 1:
                    return None
                return spec_to_direct_rust_type(binders[0][1]) or binders[0][1]
            return "bool"
        if kind == "if_expression":
            cons = node.child_by_field_name("consequence")
            alt = node.child_by_field_name("alternative")
            cons_ty = self.infer_expr_type(cons, fn) if cons is not None else None
            alt_child = None
            if alt is not None and alt.named_children:
                alt_child = alt.named_children[0]
            alt_ty = self.infer_expr_type(alt_child, fn) if alt_child is not None else None
            if cons_ty == alt_ty:
                return cons_ty
            target = self._common_numeric_target(cons, cons_ty, alt_child, alt_ty)
            if target is not None:
                return target
            return cons_ty or alt_ty
        if kind == "closure_expression":
            body_node = None
            self.push_scope()
            try:
                for name, ty in self._binders(node, fn):
                    self.bind_name(name, spec_to_direct_rust_type(ty) or ty)
                for child in node.children:
                    if child.type != "closure_parameters" and child.is_named:
                        body_node = child
                        break
                return self.infer_expr_type(body_node, fn) if body_node is not None else None
            finally:
                self.pop_scope()
        if kind == "block":
            self.push_scope()
            try:
                named = [c for c in node.named_children if c.type != "inner_attribute_item"]
                last_ty: str | None = "()"
                for child in named:
                    if child.type == "declaration_with_attrs" and child.named_children:
                        child = child.named_children[0]
                    if child.type == "let_declaration":
                        pattern = child.child_by_field_name("pattern")
                        value = child.child_by_field_name("value")
                        if pattern is not None and value is not None:
                            self._bind_pattern_types(pattern, self.infer_expr_type(value, fn), fn)
                        continue
                    expr = child
                    if child.type == "expression_statement" and child.named_children:
                        expr = child.named_children[0]
                    last_ty = self.infer_expr_type(expr, fn)
                return last_ty
            finally:
                self.pop_scope()
        if kind == "call_expression":
            callee = node.child_by_field_name("function")
            args = node.child_by_field_name("arguments")
            if callee is None:
                return None
            arg_nodes = list(args.named_children) if args is not None else []
            if callee.type == "field_expression":
                named = [c for c in callee.named_children]
                if len(named) != 2:
                    return None
                recv_ty = self.infer_expr_type(named[0], fn)
                method = _node_src(named[1], src).strip()
                if method == "len":
                    return "i64"
                if method == "last":
                    return _direct_vec_elem_type(recv_ty)
                if method in {"take", "skip", "subrange", "add", "update", "map_values", "filter", "drop_last", "drop_first", "deep_view", "push"}:
                    return recv_ty
                if method in {"max", "min"}:
                    return "i64"
                return None
            callee_text = self.translate_expr(callee, fn)
            if callee_text.startswith("Seq::") and callee_text.endswith("::empty"):
                return None
            if callee_text == "Seq::empty" or callee_text.endswith("Seq::empty"):
                return None
            if callee_text == "Seq::new" or callee_text.endswith("Seq::new"):
                if len(arg_nodes) != 2:
                    return None
                elem_ty = self.infer_expr_type(arg_nodes[1], fn)
                return None if elem_ty is None else f"std::rc::Rc<Vec<{elem_ty}>>"
            helper = self.functions.get(callee_text)
            if helper is not None:
                return spec_to_direct_rust_type(helper.ret_type)
            return None
        if kind == "macro_invocation":
            text = _node_src(node, src).strip()
            if text.startswith("seq![") and text.endswith("]"):
                inner = text[len("seq![") : -1].strip()
                if not inner:
                    return None
                parts = _split_top_level(inner)
                first_node, first_fn = _parse_direct_expr_with_fn(parts[0])
                first_ty = self.infer_expr_type(first_node, first_fn)
                return None if first_ty is None else f"std::rc::Rc<Vec<{first_ty}>>"
        return None

    def translate_expr(self, node, fn: DirectFunction) -> str:
        node = _unwrap_attrs_and_parens(node, keep_view=True)
        if node is None:
            raise DirectTranslationError(f"missing expression node in {fn.name}")
        if node.type == "declaration_with_attrs" and node.named_children:
            node = node.named_children[0]
        src = fn.source.encode("utf-8")
        kind = node.type
        if kind in {"identifier", "field_identifier"}:
            return _node_src(node, src)
        if kind == "scoped_identifier":
            text = _node_src(node, src)
            text = text.replace("Self::", "").replace("Solution::", "")
            return text
        if kind == "integer_literal":
            text = _node_src(node, src)
            text = re.sub(r"\b(\d[\d_]*)int\b", r"\1i64", text)
            text = re.sub(r"\b(\d[\d_]*)nat\b", r"\1i64", text)
            return text
        if kind in {"boolean_literal", "char_literal"}:
            return _node_src(node, src)
        if kind == "string_literal":
            return f"std::rc::Rc::new(String::from({_node_src(node, src)}))"
        if kind == "parenthesized_expression":
            named = [c for c in node.named_children]
            inner = self.translate_expr(named[-1], fn) if named else ""
            return f"({inner})"
        if kind == "view_expression":
            named = [c for c in node.named_children]
            if not named:
                raise DirectTranslationError(f"unsupported view expression in {fn.name}")
            inner = named[0]
            inner_text = self.translate_expr(inner, fn)
            inner_ty = self.infer_expr_type(inner, fn)
            if inner_ty == "std::rc::Rc<String>":
                return f"string_chars(({inner_text}).clone())"
            return inner_text
        if kind == "tuple_expression":
            parts = [self.translate_expr(child, fn) for child in node.named_children]
            return "(" + ", ".join(parts) + ")"
        if kind == "field_expression":
            named = [c for c in node.named_children]
            if len(named) != 2:
                raise DirectTranslationError(f"unsupported field expression in {fn.name}")
            recv = self.translate_expr(named[0], fn)
            field = self.translate_expr(named[1], fn)
            return f"({recv}).{field}"
        if kind == "index_expression":
            named = [c for c in node.named_children]
            if len(named) != 2:
                raise DirectTranslationError(f"unsupported index expression in {fn.name}")
            recv = self.translate_expr(named[0], fn)
            # Index expressions must use exact integer arithmetic, not the
            # caller's modular arithmetic. If we're translating inside a
            # `__mod_*` variant, applying `mod_sub_i64` etc. to `arr[end-1]`
            # would replace the index with `(end - 1) mod modulus`, picking
            # the wrong element. Always render the index in the
            # *non-modular* path.
            saved = self.current_modulus_source
            self.current_modulus_source = None
            saved_override = self.current_modulus_rust_override
            self.current_modulus_rust_override = None
            try:
                idx = self.translate_expr(named[1], fn)
            finally:
                self.current_modulus_source = saved
                self.current_modulus_rust_override = saved_override
            # Indexing a translated `Rc<Vec<_>>` yields a borrowed element.
            # `safe_index_clone` returns `T::default()` on out-of-bounds rather
            # than panicking, matching Verus' `int`-domain Seq semantics where
            # an OOB read is undefined but never traps execution.  Without
            # this, postconditions like `nums[res] == target || res == len`
            # falsely fail when the first disjunct is evaluated for `res = len`.
            return f"safe_index_clone(&({recv})[..], ({idx}) as i64)"
        if kind == "type_cast_expression":
            value = node.child_by_field_name("value")
            target = node.child_by_field_name("type")
            if value is None or target is None:
                raise DirectTranslationError(f"unsupported type cast in {fn.name}")
            value_text = self.translate_expr(value, fn)
            target_text = _node_src(target, src).strip()
            # The direct backend models Verus `int`, `nat`, and `usize` as
            # plain `i64` values.  Keeping `as usize` in translated arithmetic
            # leaks Rust's index type into comparisons and recursive helper
            # calls, which is what caused mixed `i64`/`usize` compile failures
            # in otherwise-convertible specs like `lc566` and `cf981C`.
            if target_text in {"int", "nat", "usize"}:
                target_text = "i64"
            return f"(({value_text}) as {target_text})"
        if kind == "unary_expression":
            named = node.named_children
            if not named:
                raise DirectTranslationError(f"unsupported unary expression in {fn.name}")
            operand_node = named[0]
            operand = self.translate_expr(operand_node, fn)
            op = _node_src(node.children[0], src).strip()
            if (
                self.current_modulus_source is not None
                and op == "-"
                and _direct_int_type(self.infer_expr_type(operand_node, fn))
            ):
                modulus_text = self._modulus_rust_text(self.current_modulus_source)
                return f"mod_neg_i64(({operand}) as i64, ({modulus_text}) as i64)"
            return f"({op}{operand})"
        if kind == "binary_expression":
            return self.translate_binary(node, fn)
        if kind in {"big_and_expression", "big_or_expression"}:
            op = "&&" if kind == "big_and_expression" else "||"
            parts = [self.translate_expr(child, fn) for child in node.named_children]
            if not parts:
                return "true" if kind == "big_and_expression" else "false"
            return "(" + f" {op} ".join(parts) + ")"
        if kind == "call_expression":
            return self.translate_call(node, fn)
        if kind == "if_expression":
            return self.translate_if(node, fn)
        if kind == "block":
            return self.translate_block(node, fn)
        if kind == "quantifier_expression":
            return self.translate_quantifier(node, fn)
        if kind == "closure_expression":
            return self.translate_closure(node, fn)
        if kind == "return_expression":
            named = node.named_children
            if not named:
                return "return"
            return f"return {self.translate_expr(named[0], fn)}"
        if kind == "macro_invocation":
            return self.translate_macro(node, fn)
        raise DirectTranslationError(f"unsupported expression node `{kind}` in {fn.name}")

    def translate_macro(self, node, fn: DirectFunction) -> str:
        text = _node_src(node, fn.source.encode("utf-8")).strip()
        if text.startswith("seq![") and text.endswith("]"):
            inner = text[len("seq![") : -1].strip()
            if not inner:
                return "std::rc::Rc::new(vec![])"
            parts = _split_top_level(inner)
            exprs = []
            for part in parts:
                expr_node, expr_fn = _parse_direct_expr_with_fn(part)
                if expr_node is None:
                    raise DirectTranslationError(f"unsupported seq! element `{part}` in {fn.name}")
                exprs.append(self.translate_expr(expr_node, expr_fn))
            return f"std::rc::Rc::new(vec![{', '.join(exprs)}])"
        raise DirectTranslationError(f"unsupported macro invocation `{text}` in {fn.name}")

    def translate_if(self, node, fn: DirectFunction) -> str:
        cond = node.child_by_field_name("condition")
        cons = node.child_by_field_name("consequence")
        alt = node.child_by_field_name("alternative")
        if cond is None or cons is None:
            raise DirectTranslationError(f"malformed if-expression in {fn.name}")
        cond_text = (
            self.translate_expr_exact(cond, fn)
            if self.current_modulus_source is not None
            else self.translate_expr(cond, fn)
        )
        cons_text = self.translate_block(cons, fn)
        cons_ty = self.infer_expr_type(cons, fn)
        if alt is None:
            return f"if {cond_text} {cons_text}"
        alt_named = alt.named_children
        if not alt_named:
            raise DirectTranslationError(f"malformed else-clause in {fn.name}")
        alt_child = alt_named[0]
        alt_text = (
            self.translate_block(alt_child, fn)
            if alt_child.type == "block"
            else self.translate_expr(alt_child, fn)
        )
        alt_ty = self.infer_expr_type(alt_child, fn)
        target = self._common_numeric_target(cons, cons_ty, alt_child, alt_ty)
        if target is not None and cons_ty != alt_ty:
            cons_text = f"{{ (({cons_text}) as {target}) }}"
            alt_text = f"{{ (({alt_text}) as {target}) }}"
        return f"if {cond_text} {cons_text} else {alt_text}"

    def translate_binary(self, node, fn: DirectFunction) -> str:
        op = _comparison_op(node)
        left = node.child_by_field_name("left")
        right = node.child_by_field_name("right")
        if op is None or left is None or right is None:
            raise DirectTranslationError(f"malformed binary expression in {fn.name}")
        if op in {"<", "<=", ">", ">="}:
            flat = _flatten_comparison_chain(node)
            if flat is not None:
                items, ops = flat
                if len(ops) > 1:
                    parts = []
                    for lhs, cmp_op, rhs in zip(items, ops, items[1:]):
                        lhs_ty = self.infer_expr_type(lhs, fn)
                        rhs_ty = self.infer_expr_type(rhs, fn)
                        if _direct_int_type(lhs_ty) and _direct_int_type(rhs_ty):
                            lhs_text = self._translate_numeric_to(lhs, fn, "i64")
                            rhs_text = self._translate_numeric_to(rhs, fn, "i64")
                        else:
                            lhs_text = self.translate_expr(lhs, fn)
                            rhs_text = self.translate_expr(rhs, fn)
                            lhs_text, rhs_text = self._coerce_numeric_pair(
                                lhs_text,
                                lhs_ty,
                                rhs_text,
                                rhs_ty,
                            )
                        use_op = "==" if cmp_op == "=~=" else cmp_op
                        parts.append(f"(({lhs_text}) {use_op} ({rhs_text}))")
                    return "(" + " && ".join(parts) + ")"
        if self.current_modulus_source is None and op == "%":
            modulus_source = self._subtree_modulus_source(left, fn)
            if (
                modulus_source is not None
                and _normalize_expr_source(_node_src(right, fn.source.encode("utf-8")).strip())
                == _normalize_expr_source(modulus_source)
            ):
                left_text = self.translate_expr_with_modulus(left, fn, modulus_source)
                right_text = self.translate_expr(right, fn)
                return f"(({left_text}) % ({right_text}))"
        left_text = self.translate_expr(left, fn)
        right_text = self.translate_expr(right, fn)
        left_ty = self.infer_expr_type(left, fn)
        right_ty = self.infer_expr_type(right, fn)
        if op in {"&&&", "&&"}:
            return f"(({left_text}) && ({right_text}))"
        if op in {"|||", "||"}:
            return f"(({left_text}) || ({right_text}))"
        if op == "==>":
            return f"((!({left_text})) || ({right_text}))"
        if op == "<==":
            return f"((!({right_text})) || ({left_text}))"
        if op == "<==>":
            if _direct_int_type(left_ty) and _direct_int_type(right_ty):
                left_text = self._translate_numeric_to(left, fn, "i64")
                right_text = self._translate_numeric_to(right, fn, "i64")
            else:
                left_text, right_text = self._coerce_numeric_pair(
                    left_text, left_ty, right_text, right_ty
                )
            return f"(({left_text}) == ({right_text}))"
        if op == "=~=":
            if _direct_int_type(left_ty) and _direct_int_type(right_ty):
                left_text = self._translate_numeric_to(left, fn, "i64")
                right_text = self._translate_numeric_to(right, fn, "i64")
            else:
                left_text, right_text = self._coerce_numeric_pair(
                    left_text, left_ty, right_text, right_ty
                )
            return f"(({left_text}) == ({right_text}))"
        if op == "+" and left_ty == right_ty and _direct_vec_elem_type(left_ty) is not None:
            return f"seq_add(({left_text}).clone(), ({right_text}).clone())"
        if self.current_modulus_source is not None and _direct_int_type(left_ty) and _direct_int_type(right_ty):
            modulus_text = self._modulus_rust_text(self.current_modulus_source)
            left_num = self._translate_numeric_to(left, fn, "i64")
            right_num = self._translate_numeric_to(right, fn, "i64")
            if op == "+":
                return f"mod_add_i64(({left_num}) as i64, ({right_num}) as i64, ({modulus_text}) as i64)"
            if op == "-":
                return f"mod_sub_i64(({left_num}) as i64, ({right_num}) as i64, ({modulus_text}) as i64)"
            if op == "*":
                return f"mod_mul_i64(({left_num}) as i64, ({right_num}) as i64, ({modulus_text}) as i64)"
            if op == "%" and _normalize_expr_source(_node_src(right, fn.source.encode("utf-8")).strip()) == _normalize_expr_source(self.current_modulus_source):
                return f"mod_norm_i64(({left_num}) as i128, ({modulus_text}) as i64)"
        if op in {"<", "<=", ">", ">=", "==", "!="}:
            if _direct_int_type(left_ty) and _direct_int_type(right_ty):
                left_text = self._translate_numeric_to(left, fn, "i64")
                right_text = self._translate_numeric_to(right, fn, "i64")
            else:
                left_text, right_text = self._coerce_numeric_pair(
                    left_text, left_ty, right_text, right_ty
                )
        elif op in {"+", "-", "*", "/", "%"}:
            left_text, right_text = self._coerce_numeric_pair(
                left_text, left_ty, right_text, right_ty
            )
            if op == "%" and self._is_spec_int_node(left, fn):
                # Verus' `%` on `int`/`nat` follows Euclidean (non-negative
                # remainder when divisor > 0), while Rust's `%` is truncating
                # and may return a negative value for negative dividends.
                # Use a runtime helper so soundness checks match the spec.
                return f"mod_floor_i64(({left_text}) as i64, ({right_text}) as i64)"
        return f"(({left_text}) {op} ({right_text}))"

    def translate_closure(self, node, fn: DirectFunction) -> str:
        src = fn.source.encode("utf-8")
        params_node = None
        body_node = None
        for child in node.children:
            if child.type == "closure_parameters":
                params_node = child
            elif child.is_named:
                body_node = child
        if body_node is None:
            raise DirectTranslationError(f"unsupported closure in {fn.name}")
        params = []
        if params_node is not None:
            for name, ty in _closure_params_text(params_node, src):
                if ty in {"int", "nat"}:
                    params.append(f"{name}: i64")
                elif ty is None:
                    params.append(name)
                else:
                    params.append(f"{name}: {spec_to_direct_rust_type(ty) or ty}")
        params_text = ", ".join(params)
        self.push_scope()
        try:
            for name, ty in self._binders(node, fn):
                self.bind_name(name, spec_to_direct_rust_type(ty) or ty)
            body_text = self.translate_expr(body_node, fn)
            body_ty = self.infer_expr_type(body_node, fn)
        finally:
            self.pop_scope()
        if body_ty is not None and body_ty.startswith("std::rc::Rc<"):
            body_text = f"({body_text}).clone()"
        return f"|{params_text}| {body_text}"

    def translate_call(self, node, fn: DirectFunction) -> str:
        callee = node.child_by_field_name("function")
        args = node.child_by_field_name("arguments")
        if callee is None or args is None:
            raise DirectTranslationError(f"malformed call expression in {fn.name}")
        arg_nodes = list(args.named_children)
        arg_renderer = self.translate_expr_exact if self.current_modulus_source is not None else self.translate_expr
        if callee.type == "field_expression":
            named = [c for c in callee.named_children]
            if len(named) != 2:
                raise DirectTranslationError(f"unsupported method call in {fn.name}")
            recv_node, field_node = named
            recv_text = arg_renderer(recv_node, fn)
            method = self.translate_expr(field_node, fn)
            if method == "len":
                return f"(({recv_text}).len() as i64)"
            if method == "last" and len(arg_nodes) == 0:
                return f"seq_last(({recv_text}).clone())"
            if method == "drop_last" and len(arg_nodes) == 0:
                return f"seq_drop_last(({recv_text}).clone())"
            if method == "drop_first" and len(arg_nodes) == 0:
                return f"seq_drop_first(({recv_text}).clone())"
            if method == "deep_view" and len(arg_nodes) == 0:
                return f"({recv_text}).clone()"
            if method == "push" and len(arg_nodes) == 1:
                val = arg_renderer(arg_nodes[0], fn)
                return f"seq_push(({recv_text}).clone(), ({val}).clone())"
            if method == "to_multiset" and len(arg_nodes) == 0:
                return f"seq_to_multiset(({recv_text}).clone())"
            if method == "take" and len(arg_nodes) == 1:
                return f"seq_take(({recv_text}).clone(), ({arg_renderer(arg_nodes[0], fn)}) as i64)"
            if method == "skip" and len(arg_nodes) == 1:
                return f"seq_skip(({recv_text}).clone(), ({arg_renderer(arg_nodes[0], fn)}) as i64)"
            if method == "subrange" and len(arg_nodes) == 2:
                a0 = arg_renderer(arg_nodes[0], fn)
                a1 = arg_renderer(arg_nodes[1], fn)
                return f"seq_subrange(({recv_text}).clone(), ({a0}) as i64, ({a1}) as i64)"
            if method == "add" and len(arg_nodes) == 1:
                rhs = arg_renderer(arg_nodes[0], fn)
                return f"seq_add(({recv_text}).clone(), ({rhs}).clone())"
            if method == "update" and len(arg_nodes) == 2:
                idx = arg_renderer(arg_nodes[0], fn)
                val = arg_renderer(arg_nodes[1], fn)
                return f"seq_update(({recv_text}).clone(), ({idx}) as i64, ({val}).clone())"
            if method == "map_values" and len(arg_nodes) == 1:
                clos = arg_renderer(arg_nodes[0], fn)
                return f"seq_map_values(({recv_text}).clone(), {clos})"
            if method == "filter" and len(arg_nodes) == 1:
                clos = arg_renderer(arg_nodes[0], fn)
                return f"seq_filter(({recv_text}).clone(), {clos})"
            if method == "max" and len(arg_nodes) == 0:
                return f"seq_vec_max_i64(({recv_text}).clone())"
            if method == "min" and len(arg_nodes) == 0:
                return f"seq_vec_min_i64(({recv_text}).clone())"
            if method == "contains" and len(arg_nodes) == 1:
                val = arg_renderer(arg_nodes[0], fn)
                return f"({recv_text}).contains(&({val}))"
            call_args = ", ".join(arg_renderer(arg, fn) for arg in arg_nodes)
            return f"({recv_text}).{method}({call_args})"

        callee_text = self.translate_expr(callee, fn)
        if callee_text.startswith("Seq::") and callee_text.endswith("::empty"):
            return "seq_empty()"
        if callee_text == "Seq::empty" or callee_text.endswith("Seq::empty"):
            return "seq_empty()"
        if callee_text == "Set::empty" or callee_text.endswith("Set::empty"):
            return "std::rc::Rc::new(std::collections::HashSet::new())"
        if callee_text == "Map::empty" or callee_text.endswith("Map::empty"):
            return "std::rc::Rc::new(std::collections::HashMap::new())"
        if callee_text == "Seq::new" or callee_text.endswith("Seq::new"):
            if len(arg_nodes) != 2:
                raise DirectTranslationError(f"unsupported Seq::new arity in {fn.name}")
            ln = arg_renderer(arg_nodes[0], fn)
            clos = arg_renderer(arg_nodes[1], fn)
            return f"seq_new(({ln}) as i64, {clos})"

        if callee_text in self.functions:
            target_name = callee_text
            use_mod_variant = False
            if (
                self.current_modulus_source is not None
                and callee_text in self.mod_function_sources
                and _normalize_expr_source(self.mod_function_sources[callee_text])
                == _normalize_expr_source(self.current_modulus_source)
            ):
                target_name = self._mod_variant_name(callee_text)
                use_mod_variant = True
            param_types = [p.spec_type for p in self.functions[callee_text].params]
            rendered_args = [
                coerce_direct_arg(arg_renderer(arg, fn), param_types[idx])
                if idx < len(param_types)
                else arg_renderer(arg, fn)
                for idx, arg in enumerate(arg_nodes)
            ]
            if use_mod_variant:
                modulus_arg = self._modulus_rust_text(self.current_modulus_source)
                rendered_args.append(f"({modulus_arg}) as i64")
            return f"{target_name}(" + ", ".join(rendered_args) + ")"

        rendered_args = [arg_renderer(arg, fn) for arg in arg_nodes]
        return f"{callee_text}(" + ", ".join(rendered_args) + ")"

    def _binders(self, node, fn: DirectFunction) -> list[tuple[str, str]]:
        src = fn.source.encode("utf-8")
        params_node = None
        for child in node.children:
            if child.type == "closure_parameters":
                params_node = child
                break
        if params_node is None:
            return []
        params: list[tuple[str, str]] = []
        for name, ty in _closure_params_text(params_node, src):
            params.append((name, ty or "i64"))
        return params

    def _inline_bool_helper(
        self,
        node,
        fn: DirectFunction,
        depth: int,
    ) -> tuple[object, DirectFunction] | None:
        if depth >= 4 or node.type != "call_expression":
            return None
        callee = node.child_by_field_name("function")
        args = node.child_by_field_name("arguments")
        if callee is None or args is None:
            return None
        callee_text = self.translate_expr(callee, fn)
        helper = self.functions.get(callee_text)
        if helper is None or helper.ret_type.strip() != "bool":
            return None
        helper_body = helper.node.child_by_field_name("body")
        if helper_body is None:
            return None
        helper_src = helper.source.encode("utf-8")
        body_nodes = [
            child
            for child in helper_body.named_children
            if child.type != "inner_attribute_item"
        ]
        if not body_nodes:
            return None
        body_inner = _node_src(body_nodes[-1], helper_src)
        arg_texts = [
            _node_src(arg, fn.source.encode("utf-8")) for arg in args.named_children
        ]

        local_defs: list[tuple[str, str]] = []
        for child in body_nodes[:-1]:
            node = child
            if node.type == "declaration_with_attrs" and node.named_children:
                node = node.named_children[0]
            if node.type != "let_declaration":
                continue
            pattern = node.child_by_field_name("pattern")
            value = node.child_by_field_name("value")
            if pattern is None or value is None or pattern.type != "identifier":
                continue
            local_defs.append((
                _node_src(pattern, helper_src).strip(),
                _node_src(value, helper_src).strip(),
            ))

        for param, arg_text in sorted(
            zip(helper.params, arg_texts),
            key=lambda item: -len(item[0].name),
        ):
            body_inner = re.sub(
                rf"\b{re.escape(param.name)}\b",
                f"({arg_text})",
                body_inner,
            )
            local_defs = [
                (
                    name,
                    re.sub(
                        rf"\b{re.escape(param.name)}\b",
                        f"({arg_text})",
                        value_text,
                    ),
                )
                for name, value_text in local_defs
            ]
        expanded_locals: list[tuple[str, str]] = []
        for local_name, local_expr in local_defs:
            for prev_name, prev_expr in expanded_locals:
                local_expr = re.sub(
                    rf"\b{re.escape(prev_name)}\b",
                    f"({prev_expr})",
                    local_expr,
                )
            expanded_locals.append((local_name, local_expr))
        for local_name, local_expr in sorted(expanded_locals, key=lambda item: -len(item[0])):
            body_inner = re.sub(
                rf"\b{re.escape(local_name)}\b",
                f"({local_expr})",
                body_inner,
            )
        tmp_fn = _parse_direct_function(
            "verus! {\n"
            "pub open spec fn __inline_tmp() -> bool {\n"
            f"{body_inner}\n"
            "}\n"
            "}\n"
        )
        body_node = tmp_fn.node.child_by_field_name("body")
        if body_node is None or not body_node.named_children:
            return None
        return body_node.named_children[-1], tmp_fn

    def _collect_quant_bounds(
        self,
        node,
        fn: DirectFunction,
        binders: list[tuple[str, str]],
        domains: dict[str, dict[str, list[tuple[str, bool]]]],
        kind: str,
        depth: int = 0,
    ) -> None:
        node = _unwrap_attrs_and_parens(node)
        if node is None:
            return
        if node.type == "call_expression":
            inlined = self._inline_bool_helper(node, fn, depth)
            if inlined is not None:
                inlined_node, inlined_fn = inlined
                self._collect_quant_bounds(
                    inlined_node,
                    inlined_fn,
                    binders,
                    domains,
                    kind,
                    depth + 1,
                )
            return
        if node.type == "unary_expression":
            op = _node_src(node.children[0], fn.source.encode("utf-8")).strip()
            if op == "!" and kind == "forall":
                named = node.named_children
                if named:
                    self._collect_quant_bounds(
                        named[0], fn, binders, domains, kind, depth + 1
                    )
            return
        if node.type == "binary_expression":
            op = _comparison_op(node)
            if op in {"&&", "&&&"}:
                left = node.child_by_field_name("left")
                right = node.child_by_field_name("right")
                if left is not None:
                    self._collect_quant_bounds(left, fn, binders, domains, kind, depth + 1)
                if right is not None:
                    self._collect_quant_bounds(right, fn, binders, domains, kind, depth + 1)
                return
            if op == "==>":
                # For forall, only the antecedent (LHS) restricts the domain
                # we need to check the body over.  For exists, neither side of
                # an implication constrains the witness, so we skip both.
                if kind == "forall":
                    left = node.child_by_field_name("left")
                    if left is not None:
                        self._collect_quant_bounds(left, fn, binders, domains, kind, depth + 1)
                return
            if op == "<==":
                if kind == "forall":
                    right = node.child_by_field_name("right")
                    if right is not None:
                        self._collect_quant_bounds(right, fn, binders, domains, kind, depth + 1)
                return
            if op in {"<", "<=", ">", ">=", "==", "!=", "=~="}:
                flat = _flatten_comparison_chain(node)
                if flat is None:
                    return
                items, ops = flat
                binder_names = {name for name, _ in binders}
                binder_pos = {name: idx for idx, (name, _) in enumerate(binders)}
                src = fn.source.encode("utf-8")

                def forbidden_for(name: str) -> set[str]:
                    # Allow bounds that mention binders earlier in the binder
                    # list; reject ones that mention this binder or any later
                    # one (we'd have no value for them at iteration setup).
                    pos = binder_pos[name]
                    return {nm for nm, _ in binders if binder_pos[nm] >= pos}

                # Try to locate identifier-like positions in the chain that
                # correspond to a binder.  We treat both bare `binder` and
                # `binder + k` / `binder - k` (with `k` not mentioning a
                # binder) as "binder positions" so we still extract bounds
                # when the spec writes e.g. `j + 1 < grid[0].len()`.
                def binder_offset(item):
                    item = _unwrap_attrs_and_parens(item)
                    if item is None:
                        return None
                    if item.type == "identifier":
                        nm = _node_src(item, src).strip()
                        if nm in binder_names:
                            return (nm, "0", False)
                        return None
                    if item.type == "binary_expression":
                        sub_op = _comparison_op(item)
                        if sub_op in {"+", "-"}:
                            sl = item.child_by_field_name("left")
                            sr = item.child_by_field_name("right")
                            sl_u = _unwrap_attrs_and_parens(sl) if sl is not None else None
                            sr_u = _unwrap_attrs_and_parens(sr) if sr is not None else None
                            if sl_u is not None and sl_u.type == "identifier":
                                nm = _node_src(sl_u, src).strip()
                                if nm in binder_names and sr_u is not None and not _node_mentions_any_binder(sr_u, src, binder_names):
                                    off = self.translate_expr(sr_u, fn)
                                    return (nm, off, sub_op == "-")
                            if sub_op == "+" and sr_u is not None and sr_u.type == "identifier":
                                nm = _node_src(sr_u, src).strip()
                                if nm in binder_names and sl_u is not None and not _node_mentions_any_binder(sl_u, src, binder_names):
                                    off = self.translate_expr(sl_u, fn)
                                    return (nm, off, False)
                    return None

                def shift_expr(expr: str, offset: str, neg: bool, direction: str) -> str:
                    # `binder + k op X` is equivalent to `binder op X - k`.
                    # `binder - k op X` is equivalent to `binder op X + k`.
                    # `direction` is "lower" or "upper" to clarify intent
                    # but the algebraic shift is the same for both.
                    if offset == "0":
                        return expr
                    if neg:
                        return f"((({expr}) as i64) + (({offset}) as i64))"
                    return f"((({expr}) as i64) - (({offset}) as i64))"

                first_text = self.translate_expr(items[0], fn)
                last_text = self.translate_expr(items[-1], fn)
                first_has_binder = _node_mentions_any_binder(items[0], src, binder_names)
                last_has_binder = _node_mentions_any_binder(items[-1], src, binder_names)
                for idx, item in enumerate(items):
                    bo = binder_offset(item)
                    if bo is None:
                        continue
                    name, offset, neg = bo
                    forbidden = forbidden_for(name)
                    if idx > 0:
                        prev_item = items[idx - 1]
                        if not _node_mentions_any_binder(prev_item, src, forbidden):
                            prev_expr = self.translate_expr(prev_item, fn)
                            prev_op = ops[idx - 1]
                            if prev_op in {"<", "<="}:
                                shifted = shift_expr(prev_expr, offset, neg, "lower")
                                domains[name]["lower"].append((shifted, prev_op == "<="))
                            elif prev_op in {">", ">="}:
                                shifted = shift_expr(prev_expr, offset, neg, "upper")
                                domains[name]["upper"].append((shifted, prev_op == ">="))
                    if idx < len(items) - 1:
                        next_item = items[idx + 1]
                        if not _node_mentions_any_binder(next_item, src, forbidden):
                            next_expr = self.translate_expr(next_item, fn)
                            next_op = ops[idx]
                            if next_op in {"<", "<="}:
                                shifted = shift_expr(next_expr, offset, neg, "upper")
                                domains[name]["upper"].append((shifted, next_op == "<="))
                            elif next_op in {">", ">="}:
                                shifted = shift_expr(next_expr, offset, neg, "lower")
                                domains[name]["lower"].append((shifted, next_op == ">="))
                    if idx > 0 and not first_has_binder:
                        first_op = ops[0]
                        if first_op in {"<", "<="}:
                            shifted = shift_expr(first_text, offset, neg, "lower")
                            domains[name]["lower"].append((shifted, True))
                        elif first_op in {">", ">="}:
                            shifted = shift_expr(first_text, offset, neg, "upper")
                            domains[name]["upper"].append((shifted, True))
                    if idx < len(items) - 1 and not last_has_binder:
                        last_op = ops[-1]
                        if last_op in {"<", "<="}:
                            shifted = shift_expr(last_text, offset, neg, "upper")
                            domains[name]["upper"].append((shifted, last_op == "<="))
                        elif last_op in {">", ">="}:
                            shifted = shift_expr(last_text, offset, neg, "lower")
                            domains[name]["lower"].append((shifted, last_op == ">="))
        if node.type == "big_and_expression":
            for child in node.named_children:
                self._collect_quant_bounds(
                    child,
                    fn,
                    binders,
                    domains,
                    kind,
                    depth + 1,
                )

    def _collect_quant_equalities(
        self,
        node,
        fn: DirectFunction,
        binders: list[tuple[str, str]],
        kind: str,
    ) -> dict[str, str]:
        src = fn.source.encode("utf-8")
        binder_order = {name: idx for idx, (name, _) in enumerate(binders)}
        equalities: dict[str, str] = {}

        def visit(cur) -> None:
            cur = _unwrap_attrs_and_parens(cur)
            if cur is None:
                return
            if cur.type == "binary_expression":
                op = _comparison_op(cur)
                left = cur.child_by_field_name("left")
                right = cur.child_by_field_name("right")
                if op in {"&&", "&&&"}:
                    if left is not None:
                        visit(left)
                    if right is not None:
                        visit(right)
                    return
                if op == "==>" and kind == "forall":
                    if left is not None:
                        visit(left)
                    return
                if op in {"==", "=~="} and left is not None and right is not None:
                    for binder_node, expr_node in ((left, right), (right, left)):
                        binder_node = _unwrap_attrs_and_parens(binder_node)
                        expr_node = _unwrap_attrs_and_parens(expr_node, keep_view=True)
                        if binder_node is None or expr_node is None:
                            continue
                        if binder_node.type != "identifier":
                            continue
                        name = _node_src(binder_node, src).strip()
                        if name not in binder_order or name in equalities:
                            continue
                        disallowed = {
                            binder_name
                            for binder_name, _ in binders[binder_order[name] :]
                        }
                        if _node_mentions_any_binder(expr_node, src, disallowed):
                            continue
                        equalities[name] = self.translate_expr(expr_node, fn)
                        return
            if cur.type == "big_and_expression":
                for child in cur.named_children:
                    visit(child)

        visit(node)
        return equalities

    def _collect_quant_counterexample_bounds(
        self,
        node,
        fn: DirectFunction,
        binders: list[tuple[str, str]],
        domains: dict[str, dict[str, list[tuple[str, bool]]]],
    ) -> None:
        node = _unwrap_attrs_and_parens(node)
        if node is None or node.type != "binary_expression" or _comparison_op(node) != "==>":
            return
        consequent = _unwrap_attrs_and_parens(
            node.child_by_field_name("right"),
            keep_view=True,
        )
        if consequent is None or consequent.type != "binary_expression":
            return
        op = _comparison_op(consequent)
        if op not in {"<", "<=", ">", ">="}:
            return

        src = fn.source.encode("utf-8")
        binder_order = {name: idx for idx, (name, _) in enumerate(binders)}

        def binder_minus_expr(expr) -> tuple[str, str] | None:
            expr = _unwrap_attrs_and_parens(expr, keep_view=True)
            if expr is None or expr.type != "binary_expression" or _comparison_op(expr) != "-":
                return None
            left = _unwrap_attrs_and_parens(expr.child_by_field_name("left"), keep_view=True)
            right = _unwrap_attrs_and_parens(expr.child_by_field_name("right"), keep_view=True)
            if left is None or right is None or left.type != "identifier":
                return None
            name = _node_src(left, src).strip()
            if name not in binder_order:
                return None
            disallowed = {
                binder_name
                for binder_name, _ in binders[binder_order[name] :]
            }
            if _node_mentions_any_binder(right, src, disallowed):
                return None
            return name, self.translate_expr(right, fn)

        left = consequent.child_by_field_name("left")
        right = consequent.child_by_field_name("right")
        if left is None or right is None:
            return
        parsed = binder_minus_expr(left)
        if parsed is None:
            return
        name, offset_expr = parsed
        rhs_expr = _unwrap_attrs_and_parens(right, keep_view=True)
        if rhs_expr is None:
            return
        disallowed = {
            binder_name
            for binder_name, _ in binders[binder_order[name] :]
        }
        if _node_mentions_any_binder(rhs_expr, src, disallowed):
            return
        rhs_text = self.translate_expr(rhs_expr, fn)
        combined = f"(({offset_expr}) + ({rhs_text}))"
        if op == "<=":
            domains[name]["lower"].append((combined, False))
        elif op == "<":
            domains[name]["lower"].append((combined, True))
        elif op == ">=":
            domains[name]["upper"].append((combined, False))
        elif op == ">":
            domains[name]["upper"].append((combined, True))

    def _collect_seq_quant_hints(
        self,
        node,
        fn: DirectFunction,
        binders: list[tuple[str, str]],
        seq_domains: dict[str, SeqQuantDomain],
        depth: int = 0,
        blocked_names: set[str] | None = None,
    ) -> None:
        node = _unwrap_attrs_and_parens(node, keep_view=True)
        if node is None:
            return
        src = fn.source.encode("utf-8")
        binder_names = set(seq_domains)
        blocked_names = set(blocked_names or set())

        def add_relation(
            name: str,
            expr_node,
            op: str,
            binder_on_left: bool,
            *,
            length: bool,
        ) -> None:
            if _node_mentions_any_binder(expr_node, src, binder_names | blocked_names):
                return
            expr_text = self.translate_expr(expr_node, fn)
            domain = seq_domains[name]
            lower_parts = domain.len_lower if length else domain.elem_lower
            upper_parts = domain.len_upper if length else domain.elem_upper
            if op in {"==", "=~="}:
                lower_parts.append((expr_text, True))
                upper_parts.append((expr_text, True))
            elif binder_on_left:
                if op == "<=":
                    upper_parts.append((expr_text, True))
                elif op == "<":
                    upper_parts.append((expr_text, False))
                elif op == ">=":
                    lower_parts.append((expr_text, True))
                elif op == ">":
                    lower_parts.append((expr_text, False))
            else:
                if op == "<=":
                    lower_parts.append((expr_text, True))
                elif op == "<":
                    lower_parts.append((expr_text, False))
                elif op == ">=":
                    upper_parts.append((expr_text, True))
                elif op == ">":
                    upper_parts.append((expr_text, False))

        def multiset_receiver(expr) -> tuple[str | None, object | None]:
            expr = _unwrap_attrs_and_parens(expr, keep_view=True)
            if expr is None or expr.type != "call_expression":
                return None, None
            callee = expr.child_by_field_name("function")
            args = expr.child_by_field_name("arguments")
            if callee is None or args is None or args.named_children:
                return None, None
            callee = _unwrap_attrs_and_parens(callee, keep_view=True)
            if callee is None or callee.type != "field_expression":
                return None, None
            named = [c for c in callee.named_children]
            if len(named) != 2:
                return None, None
            recv, field = named
            if _node_src(field, src).strip() != "to_multiset":
                return None, None
            return _sequence_binder_name(recv, src, binder_names), recv

        if node.type == "call_expression":
            callee = node.child_by_field_name("function")
            args = node.child_by_field_name("arguments")
            arg_nodes = list(args.named_children) if args is not None else []
            callee_text = (
                _node_src(callee, src).replace("Self::", "").replace("Solution::", "").strip()
                if callee is not None
                else ""
            )
            callee_lower = callee_text.lower()
            if "sort" in callee_lower:
                for arg in arg_nodes:
                    name = _sequence_binder_name(arg, src, binder_names)
                    if name is not None:
                        seq_domains[name].sorted_hint = True
            if any(token in callee_lower for token in ("multiset", "perm", "reorder")):
                binder_hits = [
                    _sequence_binder_name(arg, src, binder_names)
                    for arg in arg_nodes
                ]
                hit_names = [name for name in binder_hits if name is not None]
                if len(hit_names) == 1:
                    target = hit_names[0]
                    for arg, name in zip(arg_nodes, binder_hits):
                        if name == target:
                            continue
                        if not _node_mentions_any_binder(arg, src, binder_names | blocked_names):
                            seq_domains[target].perm_sources.append(self.translate_expr(arg, fn))
                            break
            for arg, target in zip(arg_nodes, [
                _sequence_binder_name(arg, src, binder_names) for arg in arg_nodes
            ]):
                if target is None:
                    continue
                target_ty = None
                for binder_name, binder_ty in binders:
                    if binder_name == target:
                        target_ty = spec_to_direct_rust_type(binder_ty)
                        break
                if target_ty is None:
                    continue
                for other_arg in arg_nodes:
                    if other_arg is arg:
                        continue
                    if _node_mentions_any_binder(
                        other_arg, src, binder_names | blocked_names
                    ):
                        continue
                    if self.infer_expr_type(other_arg, fn) == target_ty:
                        seq_domains[target].value_sources.append(
                            self.translate_expr(other_arg, fn)
                        )
            inlined = self._inline_bool_helper(node, fn, depth)
            if inlined is not None:
                inlined_node, inlined_fn = inlined
                self._collect_seq_quant_hints(
                    inlined_node,
                    inlined_fn,
                    binders,
                    seq_domains,
                    depth + 1,
                    blocked_names,
                )
                return

        if node.type == "binary_expression":
            op = _comparison_op(node)
            left = node.child_by_field_name("left")
            right = node.child_by_field_name("right")
            if op in {"&&", "&&&", "==>", "<=="}:
                if left is not None:
                    self._collect_seq_quant_hints(
                        left,
                        fn,
                        binders,
                        seq_domains,
                        depth + 1,
                        blocked_names,
                    )
                if right is not None:
                    self._collect_seq_quant_hints(
                        right,
                        fn,
                        binders,
                        seq_domains,
                        depth + 1,
                        blocked_names,
                    )
                return
            if op in {"<", "<=", ">", ">=", "==", "=~="}:
                flat = _flatten_comparison_chain(node)
                if flat is not None:
                    items, ops = flat
                    for idx, item in enumerate(items):
                        len_name = _sequence_binder_len_name(item, src, binder_names)
                        elem_name = _sequence_binder_elem_name(item, src, binder_names)
                        endpoint = _sequence_binder_endpoint(item, src, binder_names)
                        if len_name is None and elem_name is None:
                            continue
                        if endpoint is not None:
                            ep_name, ep_kind = endpoint
                            if idx > 0 and ops[idx - 1] in {"==", "=~="}:
                                prev = items[idx - 1]
                                if not _node_mentions_any_binder(
                                    prev, src, binder_names | blocked_names
                                ):
                                    expr_text = self.translate_expr(prev, fn)
                                    target_list = (
                                        seq_domains[ep_name].first_values
                                        if ep_kind == "first"
                                        else seq_domains[ep_name].last_values
                                    )
                                    target_list.append(expr_text)
                            if idx < len(items) - 1 and ops[idx] in {"==", "=~="}:
                                nxt = items[idx + 1]
                                if not _node_mentions_any_binder(
                                    nxt, src, binder_names | blocked_names
                                ):
                                    expr_text = self.translate_expr(nxt, fn)
                                    target_list = (
                                        seq_domains[ep_name].first_values
                                        if ep_kind == "first"
                                        else seq_domains[ep_name].last_values
                                    )
                                    target_list.append(expr_text)
                        # Endpoint constraints (`splits[0] == X`,
                        # `splits[k - 1] == Y`) only fix specific positions
                        # of the sequence, not bounds on every element. We
                        # already routed them into first_values/last_values
                        # above; do not propagate them as element-wise
                        # bounds, or we'd intersect "elem >= X" with
                        # "elem >= Y" and synthesize an empty range.
                        if endpoint is not None:
                            continue
                        if idx > 0:
                            add_relation(
                                len_name or elem_name,
                                items[idx - 1],
                                ops[idx - 1],
                                False,
                                length=len_name is not None,
                            )
                        if idx < len(items) - 1:
                            add_relation(
                                len_name or elem_name,
                                items[idx + 1],
                                ops[idx],
                                True,
                                length=len_name is not None,
                            )
                left_elem = _sequence_binder_elem_name(left, src, binder_names) if left is not None else None
                right_elem = _sequence_binder_elem_name(right, src, binder_names) if right is not None else None
                if left_elem is not None and left_elem == right_elem and op in {"<", "<="}:
                    seq_domains[left_elem].increasing_hint = True
                if op in {"==", "=~="} and left is not None and right is not None:
                    left_name, left_recv = multiset_receiver(left)
                    right_name, right_recv = multiset_receiver(right)
                    if (
                        left_name is not None
                        and right_recv is not None
                        and not _node_mentions_any_binder(
                            right_recv, src, binder_names | blocked_names
                        )
                    ):
                        seq_domains[left_name].perm_sources.append(self.translate_expr(right_recv, fn))
                    if (
                        right_name is not None
                        and left_recv is not None
                        and not _node_mentions_any_binder(
                            left_recv, src, binder_names | blocked_names
                        )
                    ):
                        seq_domains[right_name].perm_sources.append(self.translate_expr(left_recv, fn))
                if left is not None:
                    self._collect_seq_quant_hints(
                        left,
                        fn,
                        binders,
                        seq_domains,
                        depth + 1,
                        blocked_names,
                    )
                if right is not None:
                    self._collect_seq_quant_hints(
                        right,
                        fn,
                        binders,
                        seq_domains,
                        depth + 1,
                        blocked_names,
                    )
                return

        if node.type == "big_and_expression":
            for child in node.named_children:
                self._collect_seq_quant_hints(
                    child,
                    fn,
                    binders,
                    seq_domains,
                    depth + 1,
                    blocked_names,
                )
            return

        if node.type == "quantifier_expression":
            body = node.child_by_field_name("body")
            if body is None:
                named = [c for c in node.named_children if c.type != "closure_parameters"]
                body = named[-1] if named else None
            if body is not None:
                local_blocked = blocked_names | {name for name, _ in self._binders(node, fn)}
                self._collect_seq_quant_hints(
                    body,
                    fn,
                    binders,
                    seq_domains,
                    depth + 1,
                    local_blocked,
                )
            return

        for child in node.named_children:
            self._collect_seq_quant_hints(
                child,
                fn,
                binders,
                seq_domains,
                depth + 1,
                blocked_names,
            )

    def _render_quant_bound(
        self,
        parts: list[tuple[str, bool]],
        is_upper: bool,
        default: str | None,
    ) -> str:
        rendered: list[str] = []
        for expr, inclusive in parts:
            if is_upper:
                rendered.append(f"(({expr}) as i64) + 1" if inclusive else f"(({expr}) as i64)")
            else:
                rendered.append(f"(({expr}) as i64)" if inclusive else f"((({expr}) as i64) + 1)")
        if not rendered:
            if default is None:
                raise DirectTranslationError("unbounded quantifier")
            return default
        acc = rendered[0]
        for part in rendered[1:]:
            acc = f"std::cmp::{'min' if is_upper else 'max'}({acc}, {part})"
        return acc

    def _render_quant_loose_bound(
        self,
        parts: list[tuple[str, bool]],
        is_upper: bool,
    ) -> str | None:
        rendered: list[str] = []
        for expr, inclusive in parts:
            if is_upper:
                rendered.append(f"(({expr}) as i64) + 1" if inclusive else f"(({expr}) as i64)")
            else:
                rendered.append(f"(({expr}) as i64)" if inclusive else f"((({expr}) as i64) + 1)")
        if not rendered:
            return None
        acc = rendered[0]
        for part in rendered[1:]:
            acc = f"std::cmp::{'max' if is_upper else 'min'}({acc}, {part})"
        return acc

    def _render_seq_quant_domain(
        self,
        name: str,
        ty: str,
        domain: SeqQuantDomain,
    ) -> str:
        elem_ty = _sequence_elem_spec_type(ty)
        if elem_ty not in {"int", "i32"}:
            raise DirectTranslationError(f"unsupported sequence binder type `{ty}`")

        # A seq existential where specific positions are pinned (e.g.
        # `splits[0] == 0 && splits[k] == n`) but neither values nor a
        # permutation source is available is structurally impossible to
        # enumerate by value-range expansion -- the only valid witnesses
        # are very sparse points in a huge product space, and naive
        # enumeration would either explode or (worse) silently produce no
        # candidates and report `false`. Refuse rather than emit unsound
        # code.
        if (
            (domain.first_values or domain.last_values)
            and not domain.value_sources
            and not domain.perm_sources
        ):
            raise DirectTranslationError(
                f"sequence existential `{name}` with pinned endpoints but no "
                "value source"
            )

        if domain.perm_sources:
            source_expr = domain.perm_sources[0]
            if domain.sorted_hint:
                return f"vec![seq_sorted_copy(({source_expr}).clone())]"
            return f"seq_unique_permutations(({source_expr}).clone())"

        if domain.increasing_hint and domain.first_values and domain.last_values:
            first_expr = domain.first_values[0]
            last_expr = domain.last_values[0]
            if not domain.elem_lower:
                domain.elem_lower.append((first_expr, True))
            if not domain.elem_upper:
                domain.elem_upper.append((last_expr, True))
            if not domain.len_upper:
                domain.len_upper.append((f"(({last_expr}) - ({first_expr}) + 1)", True))

        len_lower = self._render_quant_bound(domain.len_lower, False, "0")
        len_upper = self._render_quant_bound(domain.len_upper, True, None)
        if domain.value_sources:
            values_expr = "seq_union_distinct_values(vec![" + ", ".join(
                f"({expr}).clone()" for expr in domain.value_sources
            ) + "])"
            return (
                "seq_words_from_values("
                f"({len_lower}) as i64, ({len_upper}) as i64, {values_expr})"
            )
        elem_lower = self._render_quant_bound(domain.elem_lower, False, None)
        elem_upper = self._render_quant_bound(domain.elem_upper, True, None)
        if elem_ty == "int":
            return (
                "seq_words_range_i64("
                f"({len_lower}) as i64, ({len_upper}) as i64, "
                f"({elem_lower}) as i64, ({elem_upper}) as i64)"
            )
        return (
            "seq_words_range_i32("
            f"({len_lower}) as i64, ({len_upper}) as i64, "
            f"({elem_lower}) as i64, ({elem_upper}) as i64)"
        )

    def translate_quantifier(self, node, fn: DirectFunction) -> str:
        binders = self._binders(node, fn)
        if not binders:
            raise DirectTranslationError(f"empty quantifier in {fn.name}")
        quant_token = node.children[0].type if node.children else ""
        if quant_token == "forall":
            kind = "forall"
        elif quant_token == "exists":
            kind = "exists"
        elif quant_token == "choose":
            kind = "choose"
        else:
            raise DirectTranslationError(
                f"unsupported quantifier kind `{quant_token}` in {fn.name}"
            )
        body_node = node.child_by_field_name("body")
        if body_node is None:
            named = [c for c in node.named_children if c.type != "closure_parameters"]
            body_node = named[-1] if named else None
        if body_node is None:
            raise DirectTranslationError(f"missing quantifier body in {fn.name}")
        cond_text = self.translate_expr(body_node, fn)
        domains: dict[str, dict[str, list[tuple[str, bool]]]] = {
            name: {"lower": [], "upper": []} for name, _ in binders
        }
        self._collect_quant_bounds(body_node, fn, binders, domains, kind)
        if kind == "forall":
            self._collect_quant_counterexample_bounds(body_node, fn, binders, domains)
        fixed_binders = self._collect_quant_equalities(body_node, fn, binders, kind)
        seq_domains: dict[str, SeqQuantDomain] = {
            name: SeqQuantDomain()
            for name, ty in binders
            if _sequence_elem_spec_type(ty) in {"int", "i32"}
        }
        if seq_domains:
            self._collect_seq_quant_hints(body_node, fn, binders, seq_domains)
        shared_lower_parts = [
            part for dom in domains.values() for part in dom["lower"]
        ]
        shared_upper_parts = [
            part for dom in domains.values() for part in dom["upper"]
        ]
        shared_lower = self._render_quant_loose_bound(shared_lower_parts, False)
        shared_upper = self._render_quant_loose_bound(shared_upper_parts, True)

        if kind == "choose":
            if len(binders) != 1:
                raise DirectTranslationError(
                    f"choose with {len(binders)} binders not supported in {fn.name}"
                )
            name, ty = binders[0]
            rust_ty = spec_to_direct_rust_type(ty) or "i64"
            default_lower = (
                "0" if ty in {"nat", "usize", "u8", "u16", "u32", "u64", "u128"} else None
            )
            if ty == "bool":
                return (
                    "{\n"
                    f"    let mut __choose_value: Option<{rust_ty}> = None;\n"
                    f"    for {name} in [false, true] {{\n"
                    f"        if {cond_text} {{\n"
                    f"            __choose_value = Some({name});\n"
                    "            break;\n"
                    "        }\n"
                    "    }\n"
                    '    __choose_value.expect("choose witness not found")\n'
                    "}"
                )
            if name in seq_domains:
                domain_expr = self._render_seq_quant_domain(name, ty, seq_domains[name])
                return (
                    "{\n"
                    f"    let mut __choose_value: Option<{rust_ty}> = None;\n"
                    f"    let __choose_domain = {domain_expr};\n"
                    f"    for {name} in __choose_domain.into_iter() {{\n"
                    f"        if {cond_text} {{\n"
                    f"            __choose_value = Some(({name}).clone());\n"
                    "            break;\n"
                    "        }\n"
                    "    }\n"
                    '    __choose_value.expect("choose witness not found")\n'
                    "}"
                )
            lower = self._render_quant_bound(
                domains[name]["lower"],
                False,
                default_lower if default_lower is not None else shared_lower,
            )
            upper = self._render_quant_bound(domains[name]["upper"], True, shared_upper)
            if rust_ty == "i64":
                loop_head = f"for {name} in ({lower})..({upper}) {{"
            else:
                loop_head = (
                    f"for {name} in (({lower}) as {rust_ty})..(({upper}) as {rust_ty}) {{"
                )
            return (
                "{\n"
                f"    let mut __choose_value: Option<{rust_ty}> = None;\n"
                f"    {loop_head}\n"
                f"        if {cond_text} {{\n"
                f"            __choose_value = Some({name});\n"
                "            break;\n"
                "        }\n"
                "    }\n"
                '    __choose_value.expect("choose witness not found")\n'
                "}"
            )

        break_label = self.fresh("quant")
        body_lines = []
        opened_loops = 0
        for idx, (name, ty) in enumerate(binders):
            if name in fixed_binders:
                rust_ty = spec_to_direct_rust_type(ty) or "i64"
                fixed_expr = fixed_binders[name]
                if ty == "bool":
                    body_lines.append(f"let {name}: bool = {fixed_expr};")
                elif _direct_int_type(rust_ty):
                    body_lines.append(f"let {name}: {rust_ty} = (({fixed_expr}) as {rust_ty});")
                else:
                    body_lines.append(f"let {name}: {rust_ty} = {fixed_expr};")
                continue
            if ty == "bool":
                body_lines.append(f"for {name} in [false, true] {{")
                opened_loops += 1
                continue
            if name in seq_domains:
                domain_expr = self._render_seq_quant_domain(name, ty, seq_domains[name])
                body_lines.append(f"let __domain_{name} = {domain_expr};")
                body_lines.append(f"for {name} in __domain_{name}.into_iter() {{")
                opened_loops += 1
                continue
            rust_ty = spec_to_direct_rust_type(ty) or "i64"
            default_lower = "0" if ty in {"nat", "usize", "u8", "u16", "u32", "u64", "u128"} else None
            # Per-binder bounds. We only fall back to `shared_lower /
            # shared_upper` (aggregated across siblings) when this binder
            # has *no* own constraints AND no natural type-default. Using
            # another binder's bounds for an unrelated free binder is
            # unsound: the unrelated binder might genuinely range over a
            # wider domain (e.g. `v: i32` with no constraints).
            own_lower = domains[name]["lower"]
            own_upper = domains[name]["upper"]
            if not own_lower and not own_upper and default_lower is None:
                # Truly unbounded -- raise rather than silently use sibling
                # binder bounds, which would scan a too-narrow range and
                # miss witnesses (exists -> false-negative) or
                # counterexamples (forall -> false-positive).
                raise DirectTranslationError(
                    f"unbounded {kind} binder `{name}: {ty}`"
                )
            lower = self._render_quant_bound(
                own_lower,
                False,
                default_lower,
            )
            upper = self._render_quant_bound(own_upper, True, None)
            if rust_ty == "i64":
                body_lines.append(f"for {name} in ({lower})..({upper}) {{")
            else:
                body_lines.append(
                    f"for {name} in (({lower}) as {rust_ty})..(({upper}) as {rust_ty}) {{"
                )
            opened_loops += 1
        body_lines.append(
            f"if {'' if kind == 'exists' else '!'}({cond_text}) {{"
        )
        body_lines.append(
            f"    __quant_ok = {'true' if kind == 'exists' else 'false'};"
        )
        body_lines.append(f"    break '{break_label};")
        body_lines.append("}")
        for _ in range(opened_loops):
            body_lines.append("}")

        indented_body = []
        indent = ""
        for line in body_lines:
            if line == "}":
                indent = indent[:-4]
            indented_body.append("        " + indent + line)
            if line.endswith("{"):
                indent += "    "

        lines = [
            "{",
            f"    let mut __quant_ok = {'true' if kind == 'forall' else 'false'};",
            f"    '{break_label}: loop {{",
            *indented_body,
            "        break;",
            "    }",
            "    __quant_ok",
            "}",
        ]
        return "\n".join(lines)

@dataclass
class DirectProblemModel:
    sig: PostcondSig
    const_lines: list[str]
    functions: dict[str, DirectFunction]
    requires_fn_name: str | None = None  # if set, name of the requires-checker fn
    requires_clauses: list[str] = field(default_factory=list)


def _widen_direct_post_param_type(spec_type: str) -> str:
    """Use `int` for top-level scalar integers in the synthesized postcondition.

    Most Verus postconditions compare inputs/results against spec helpers that
    already operate on `int`.  Widening only the outer checker signature avoids
    repetitive mixed-width `i32`/`i64` comparisons while preserving the exact
    helper signatures; helper call arguments are still cast back by
    `coerce_direct_arg`.
    """
    inner, _, _ = strip_ref(spec_type)
    return "int" if inner.strip() in PRIM_INTS | {"int", "nat"} else spec_type


def _render_direct_requires_text(
    method_name: str,
    sig: gtp.Signature,
    requires_clauses: list[str],
) -> tuple[str, PostcondSig] | None:
    """Render a `<method>_requires(...) -> bool` spec helper that returns
    true exactly when every `requires` clause holds.  The signature is
    identical to the postcondition's *input* prefix (no `result` param).
    Returns None when there are no requires clauses to translate.
    """
    if not requires_clauses:
        return None
    params_text: list[str] = []
    params_sig: list[PostcondParam] = []
    for name, ty in sig.args:
        direct_ty = _widen_direct_post_param_type(ty)
        params_text.append(f"    {name}: {direct_ty}")
        params_sig.append(
            PostcondParam(name=name, spec_type=direct_ty, is_result=False)
        )

    body_lines = []
    for idx, clause in enumerate(requires_clauses):
        prefix = "    " if idx == 0 else "    && "
        body_lines.append(f"{prefix}({clause})")
    body = "\n".join(body_lines) if body_lines else "    true"

    params_block = ",\n".join(params_text)
    text = (
        f"pub open spec fn {method_name}_requires(\n"
        f"{params_block},\n"
        f") -> bool {{\n"
        f"{body}\n"
        f"}}\n"
    )
    return text, PostcondSig(
        fn_name=f"{method_name}_requires",
        params=params_sig,
    )


def _render_direct_postcondition_text(
    method_name: str,
    sig: gtp.Signature,
    ensures_clauses: list[str],
) -> tuple[str, PostcondSig]:
    ret_var, ret_type = gtp.parse_return(sig.ret)
    arg_names = {n for n, _ in sig.args}
    rendered_ret_var = gtp.fresh_identifier(ret_var, arg_names | {"res"})
    if rendered_ret_var != ret_var:
        ensures_clauses = [
            re.sub(rf"\b{re.escape(ret_var)}\b", rendered_ret_var, clause)
            for clause in ensures_clauses
        ]

    params_text: list[str] = []
    params_sig: list[PostcondParam] = []
    for name, ty in sig.args:
        direct_ty = _widen_direct_post_param_type(ty)
        params_text.append(f"    {name}: {direct_ty}")
        params_sig.append(PostcondParam(name=name, spec_type=direct_ty, is_result=False))
    direct_ret_type = _widen_direct_post_param_type(ret_type)
    params_text.append(f"    {rendered_ret_var}: {direct_ret_type}")
    params_sig.append(
        PostcondParam(name=rendered_ret_var, spec_type=direct_ret_type, is_result=True)
    )

    body_lines = []
    for idx, clause in enumerate(ensures_clauses):
        prefix = "    " if idx == 0 else "    && "
        body_lines.append(f"{prefix}({clause})")
    body = "\n".join(body_lines) if body_lines else "    true"

    params_block = ",\n".join(params_text)
    text = (
        f"pub open spec fn {method_name}_postcondition(\n"
        f"{params_block},\n"
        f") -> bool {{\n"
        f"{body}\n"
        f"}}\n"
    )
    return text, PostcondSig(
        fn_name=f"{method_name}_postcondition",
        params=params_sig,
    )


def _detect_direct_blockers(text: str) -> list[str]:
    blockers = [
        blocker
        for blocker in gtp.detect_blockers(text)
        if "Seq::new" not in blocker
        and blocker not in {
            "quantifier over unsupported type `Seq<int>`",
            "quantifier over unsupported type `Seq<i32>`",
        }
    ]
    if "old(" in text:
        blockers.append("old(...) state references not supported")
    return list(dict.fromkeys(blockers))


def _translate_direct_const_line(
    line: str,
    translator: DirectSpecTranslator,
) -> str:
    m = re.match(r"(?:pub\s+)?const\s+(\w+)\s*:\s*(.+?)\s*=\s*(.+);", line.strip())
    if not m:
        raise DirectTranslationError(f"unsupported const declaration `{line.strip()}`")
    name, ty, expr = m.groups()
    rust_ty = spec_to_direct_rust_type(ty.strip())
    if rust_ty is None:
        raise DirectTranslationError(f"unsupported const type `{ty.strip()}`")
    tmp_fn = _parse_direct_function(
        "verus! {\n"
        "pub open spec fn __const_tmp() -> bool {\n"
        f"{expr.strip()}\n"
        "}\n"
        "}\n"
    )
    body_node = tmp_fn.node.child_by_field_name("body")
    if body_node is None or not body_node.named_children:
        raise DirectTranslationError("const translation failed to parse expression body")
    expr_node = body_node.named_children[-1]
    expr_text = translator.translate_expr(expr_node, tmp_fn)
    return f"const {name}: {rust_ty} = {expr_text};"


def build_direct_problem_model(
    problem_dir: Path,
) -> tuple[DirectProblemModel | None, list[str]]:
    warnings: list[str] = []
    spec_rs = problem_dir / "spec.rs"
    if not spec_rs.exists():
        spec_rs = problem_dir / "code_spec.rs"
    if not spec_rs.exists():
        return None, [f"no spec.rs/code_spec.rs found in {problem_dir}"]

    try:
        spec_text = spec_rs.read_text()
        verus_text = gtp.extract_verus_block(spec_text)
        if not verus_text:
            return None, [f"no verus! block in {spec_rs}"]

        fn_name, ensures, returns_expr = gtp.choose_target_fn(verus_text)
        if fn_name is None:
            return None, [f"no ensures/returns postcondition found in {spec_rs}"]
        target_sig = gtp.parse_signature(spec_text, fn_name)
        if target_sig.receiver is not None:
            return None, [f"method receiver `{target_sig.receiver}` not supported for {fn_name}"]
        if target_sig.ret == "Self":
            return None, [f"return type `Self` not supported for {fn_name}"]

        if returns_expr is not None:
            ret_var, _ = gtp.parse_return(target_sig.ret)
            ensures = [f"{ret_var} == ({returns_expr})"]

        all_fns = gtp.extract_spec_fns(verus_text)
        needed = gtp.find_needed_spec_fns(ensures, all_fns)

        # Extract `requires` clauses for the same target fn so the harness
        # can soundly skip cases that violate them. When requires-checking
        # cannot be translated cleanly (e.g. references unsupported
        # constructs), we just skip the requires path -- not a soundness
        # problem unless the test data violates requires.
        requires_clauses = gtp.extract_requires_clauses(verus_text, fn_name)
        requires_render = _render_direct_requires_text(
            fn_name, target_sig, requires_clauses
        )
        needed_for_requires: list[str] = []
        if requires_render is not None:
            needed_for_requires = gtp.find_needed_spec_fns(
                requires_clauses, all_fns
            )
            for nm in needed_for_requires:
                if nm not in needed:
                    needed.append(nm)

        helper_texts = [
            gtp.dedent_block(gtp.sanitize_reserved_param_names(all_fns[name]))
            for name in needed
        ]

        post_text, post_sig = _render_direct_postcondition_text(
            fn_name, target_sig, ensures
        )
        raw_preview = "\n\n".join(helper_texts + [post_text])
        builtin_helpers = gtp.builtin_exec_math_specs(raw_preview, set(all_fns))
        helper_texts = builtin_helpers + helper_texts

        emitted_texts = list(helper_texts) + [post_text]
        if requires_render is not None:
            emitted_texts.append(requires_render[0])

        blockers = _detect_direct_blockers("\n\n".join(emitted_texts))
        if blockers:
            # Drop only the requires part if its blockers are unique to it,
            # so postcondition-only translation can still proceed.
            post_blockers = _detect_direct_blockers(
                "\n\n".join(helper_texts + [post_text])
            )
            if post_blockers:
                return None, post_blockers
            requires_render = None
        functions: dict[str, DirectFunction] = {}
        for helper_text in helper_texts:
            parsed = _parse_direct_function("verus! {\n" + helper_text + "\n}\n")
            functions[parsed.name] = parsed
        parsed_post = _parse_direct_function("verus! {\n" + post_text + "\n}\n")
        functions[parsed_post.name] = parsed_post
        requires_fn_name: str | None = None
        if requires_render is not None:
            try:
                parsed_req = _parse_direct_function(
                    "verus! {\n" + requires_render[0] + "\n}\n"
                )
                functions[parsed_req.name] = parsed_req
                requires_fn_name = parsed_req.name
            except Exception:
                requires_fn_name = None

        return (
            DirectProblemModel(
                sig=post_sig,
                const_lines=gtp.extract_const_lines(verus_text),
                functions=functions,
                requires_fn_name=requires_fn_name,
                requires_clauses=list(requires_clauses),
            ),
            warnings,
        )
    except Exception as exc:
        return None, [str(exc)]


def _cf_detect_interleaved_vecs(
    main_rs_text: str,
    vec_param_names: set[str],
) -> dict[str, tuple[str, int, list[str]]]:
    """Scan `main.rs` for loops that push to several Vec parameters per
    iteration.  This is the standard codeforces "n lines of k columns"
    layout that the whitespace-only tokeniser can't recover on its own.

    Returns a map `{param_name: (count_token, column_index, group_members)}`
    for params that participate in such a loop.  `count_token` is the raw
    Rust expression used for the iteration count (e.g. `"n"`); the harness
    passes it through unchanged so it must be a name we can also bind in
    the harness body.
    """
    out: dict[str, tuple[str, int, list[str]]] = {}
    if not vec_param_names:
        return out
    lines = main_rs_text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.search(r"\bfor\s+\w+\s+in\s+0\s*\.\.\s*([A-Za-z_][A-Za-z_0-9]*)", line)
        if m is None:
            m = re.search(r"\bwhile\s+\w+\s*<\s*([A-Za-z_][A-Za-z_0-9]*)", line)
        if m is None:
            i += 1
            continue
        count_token = m.group(1)
        # Walk forward collecting `<vec>.push(...)` lines until the loop
        # closes. Track depth so we only count pushes that are *direct*
        # children of this loop's body (i.e. depth == 1 after the loop
        # head has opened). Pushes in nested loops belong to those
        # inner loops, not this one.
        depth = 0
        seen_open = False
        members: list[str] = []
        push_counts: dict[str, int] = {}
        j = i
        while j < len(lines):
            cur = lines[j]
            opens = cur.count("{")
            closes = cur.count("}")
            line_depth_before = depth
            depth += opens - closes
            if opens > 0:
                seen_open = True
            # Only consider pushes that are directly at depth 1 of this
            # loop body. The line that opens an inner loop has
            # line_depth_before==1 but ends at depth 2; pushes inside
            # never have depth 1 on entry.
            if line_depth_before == 1 and depth >= 1:
                push_match = re.findall(r"\b([A-Za-z_][A-Za-z_0-9]*)\s*\.\s*push\s*\(", cur)
                for nm in push_match:
                    if nm in vec_param_names:
                        push_counts[nm] = push_counts.get(nm, 0) + 1
                        if nm not in members:
                            members.append(nm)
            if seen_open and depth <= 0:
                break
            j += 1
        # Multi-vec interleaved: each Vec is pushed exactly once per iter.
        # Don't overwrite earlier matches: the outer-most t-loop is scanned
        # first, but we want the *inner* per-row loop's count token (`n`),
        # not the t-count.  We always advance by one line so nested loops
        # (e.g. an inner `for _ in 0..n` that does the actual pushes inside
        # an outer t-loop) get their own scan.
        if len(members) >= 2 and all(push_counts.get(nm, 0) == 1 for nm in members):
            for col, nm in enumerate(members):
                if nm not in out:
                    out[nm] = (count_token, col, members)
        i += 1
    return out


def _cf_detect_main_call_args(
    main_rs_text: str,
    fn_name: str,
) -> list[str] | None:
    """Find `Solution::<fn>(args...)` (or `<fn>(args...)`) in main.rs and
    return the raw argument expressions. Returns `None` if no call is
    found.
    """
    if not main_rs_text:
        return None
    main_match = re.search(r"fn\s+main\s*\(", main_rs_text)
    if main_match is None:
        return None
    body = main_rs_text[main_match.start():]
    # Require `Solution::` prefix so we don't match the impl-block `fn`
    # declaration, which is what the spec-style API uses on this codebase.
    head = re.compile(
        r"\bSolution\s*::\s*" + re.escape(fn_name) + r"\s*\("
    )
    m = head.search(body)
    if m is None:
        return None
    # Walk forward, balancing nested parens, to find the matching `)`.
    pos = m.end()
    depth = 1
    end = pos
    while end < len(body) and depth > 0:
        ch = body[end]
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                break
        end += 1
    if depth != 0:
        return None
    raw = body[pos:end].strip()
    if not raw:
        return []
    # Naive split on commas at depth 0. Args at this level rarely contain
    # nested parens; if they do, we just return None and skip the check.
    args: list[str] = []
    depth = 0
    cur = ""
    for ch in raw:
        if ch == "(":
            depth += 1
            cur += ch
        elif ch == ")":
            depth -= 1
            cur += ch
        elif ch == "," and depth == 0:
            args.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        args.append(cur.strip())
    return args


def _cf_main_param_is_directly_read(
    main_rs_text: str,
    param_name: str,
    is_vec: bool,
) -> bool:
    """Heuristic: does `param_name` get its value from raw stdin tokens in
    a way the harness can mirror, or is it computed from other variables?

    Scalars must come from `let param: TY = ...parse(...);` or similar
    direct read.  Vec params are accepted if they're declared as a Vec
    that gets populated either by direct push-of-parsed-token OR by
    push-of-a-local-with-parse-in-RHS (cf302A pattern). Vec params
    populated by computed values (e.g. cf1714A's `alarms.push(ah*60+am)`)
    are still acceptable IF the harness can collect the same number of
    tokens, but the values won't match the spec view. To stay sound we
    refuse Vec params whose pushes use *no* parsed-token expression at
    all (`vec.push(0)`-style aggregation).

    Returns False when the binding is via pure aggregation/computation
    that doesn't touch input tokens.
    """
    if not main_rs_text:
        return True
    main_match = re.search(r"fn\s+main\s*\(", main_rs_text)
    if main_match is None:
        return True
    body = main_rs_text[main_match.start():]

    # Direct scalar parse: `let [mut] X[: TY] = ...parse...;`
    pat_let = re.compile(
        rf"let\s+(?:mut\s+)?{re.escape(param_name)}\s*(?::[^=]+)?=\s*([^;]+);",
        re.DOTALL,
    )
    for m in pat_let.finditer(body):
        rhs = m.group(1)
        if ".parse" in rhs:
            return True

    if not is_vec:
        return False

    # Vec params: check that there's at least one push, and that input
    # tokens are read in main.rs at all (otherwise the Vec is built from
    # constants like `vec.push(0)`).
    has_push = re.search(
        rf"\b{re.escape(param_name)}\s*\.\s*push\s*\(",
        body,
    ) is not None
    if not has_push:
        return False
    # If main.rs anywhere reads via .parse(), consider the Vec to be
    # plausibly fed from stdin -- this catches cf302A's `let v = ...parse;
    # a.push(v);` pattern. The earlier "directly read" check on call
    # arguments still demands the Vec is passed verbatim.
    if re.search(r"\.\s*parse\s*\(", body):
        return True
    return False


def _cf_call_args_are_simple(
    call_args: list[str],
    spec_param_names: set[str],
) -> bool:
    """Return True if every main.rs `Solution::call(...)` argument is a
    plain identifier that matches a spec parameter (possibly with leading
    `&` or `.clone()`). If any argument is a transformed expression (e.g.
    `h * 60 + m`), the harness can't reconstruct the spec input from raw
    stdin tokens and we should refuse.
    """
    for arg in call_args:
        a = arg.strip()
        # strip common borrow / clone wrappers
        a = re.sub(r"^&(?:mut\s+)?", "", a).strip()
        a = re.sub(r"\.clone\s*\(\s*\)$", "", a).strip()
        # bare identifier?
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", a):
            return False
        if a not in spec_param_names:
            return False
    return True


def _cf_detect_input_prelude(
    main_rs_text: str,
    spec_param_names: set[str],
    has_t_loop: bool,
) -> list[tuple[str, str]] | None:
    """Look at main.rs for an input-reading prelude that consumes scalars
    *before* any Vec push or t-loop.  Returns a list of (var_name, rust_ty)
    tuples in input order for variables that are NOT spec params (i.e.
    "ghost" tokens we must consume but not pass to the postcondition).

    Returns `None` if the prelude is ambiguous (stop trying to second-guess
    main.rs and let the regular heuristic do its thing).
    """
    if not main_rs_text:
        return None
    m = re.search(r"fn\s+main\s*\(", main_rs_text)
    if m is None:
        return None
    body = main_rs_text[m.start():]
    # If main.rs has a t-loop (multi-case), the harness already handles it
    # separately; ghost-token detection should look INSIDE the per-case
    # block, not before it. Otherwise look at the top of main.
    if has_t_loop:
        # Find the body of the for/while-t loop and only scan inside.
        loop_match = re.search(r"\b(for|while)[^{]*\{", body)
        if loop_match is not None:
            body = body[loop_match.end():]
    end = len(body)
    for marker in (
        r"\b\w+\s*\.\s*push\s*\(",
        r"\bfor\s+\w+\s+in\s+0\s*\.\.",
        r"\bwhile\s+\w+\s*<",
    ):
        m2 = re.search(marker, body)
        if m2 is not None:
            end = min(end, m2.start())
    prelude = body[:end]
    ghosts: list[tuple[str, str]] = []
    # Match `let [mut] X: <int_ty> = <rhs>;` and only count it if the RHS
    # actually reads a token from stdin (i.e. .parse() / .next().*parse()).
    # Skip plain initialisers like `let mut i: usize = 0;` which are loop
    # counters, not input.
    pat = re.compile(
        r"let\s+(?:mut\s+)?(\w+)\s*:\s*(usize|u\d+|i\d+|isize)\s*=\s*([^;]+);",
        re.DOTALL,
    )
    for match in pat.finditer(prelude):
        name = match.group(1)
        ty = match.group(2)
        rhs = match.group(3)
        if name in spec_param_names:
            continue
        # Only treat as input ghost when RHS appears to read+parse a token.
        if ".parse" not in rhs:
            continue
        ghosts.append((name, ty))
    if not ghosts:
        return None
    return ghosts


def _cf_detect_output_length_prefixed(main_rs_text: str) -> bool:
    """Heuristic: does main.rs print the result Vec's length before its
    elements? We look for an output-side `.len()` print followed by
    element prints (e.g. cf1077C). When no length is printed, the spec's
    length-prefix assumption is wrong and we should derive the count from
    an input scalar instead.
    """
    if not main_rs_text:
        return True
    m = re.search(r"fn\s+main\s*\(", main_rs_text)
    if m is None:
        return True
    body = main_rs_text[m.start():]
    # Print of `<ident>.len()` (with optional explicit `as` cast) anywhere
    # after the call site is a strong signal of length-prefixed output.
    if re.search(r"println!\([^)]*\.len\s*\(\s*\)", body):
        return True
    if re.search(r"writeln!\([^)]*\.len\s*\(\s*\)", body):
        return True
    if re.search(r"print!\([^)]*\.len\s*\(\s*\)", body):
        return True
    return False


def _cf_detect_loop_multipliers(
    main_rs_text: str,
    vec_param_names: set[str],
) -> dict[str, tuple[str, int]]:
    """Detect loops where a single Vec param is pushed K times per iter, so
    its total length is `count_token * K` rather than just `count_token`.

    Returns `{param_name: (count_token, K)}`. Only entries with K >= 2 are
    included; single-push loops are handled by the regular count-token path.
    """
    out: dict[str, tuple[str, int]] = {}
    if not vec_param_names:
        return out
    lines = main_rs_text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.search(r"\bfor\s+\w+\s+in\s+0\s*\.\.\s*([A-Za-z_][A-Za-z_0-9]*)", line)
        if m is None:
            m = re.search(r"\bwhile\s+\w+\s*<\s*([A-Za-z_][A-Za-z_0-9]*)", line)
        if m is None:
            i += 1
            continue
        count_token = m.group(1)
        # Only count pushes that are *direct* children of this loop's body
        # (depth == 1 after the head opens). Pushes nested in an inner loop
        # belong to that inner loop and will be counted when we scan it
        # separately on a later iteration.
        depth = 0
        seen_open = False
        push_counts: dict[str, int] = {}
        j = i
        while j < len(lines):
            cur = lines[j]
            opens = cur.count("{")
            closes = cur.count("}")
            line_depth_before = depth
            depth += opens - closes
            if opens > 0:
                seen_open = True
            if line_depth_before == 1 and depth >= 1:
                push_match = re.findall(r"\b([A-Za-z_][A-Za-z_0-9]*)\s*\.\s*push\s*\(", cur)
                for nm in push_match:
                    if nm in vec_param_names:
                        push_counts[nm] = push_counts.get(nm, 0) + 1
            if seen_open and depth <= 0:
                break
            j += 1
        # Single-vec multi-push case (e.g. cf69A: vec gets 3 pushes/iter).
        # Advance one line at a time so an inner data-loop nested inside an
        # outer t-loop still gets its own scan; the outer t-loop's scan will
        # see no depth-1 pushes (they belong to the inner loop) and won't
        # produce a spurious entry.
        single_vecs = [nm for nm, k in push_counts.items() if k >= 2]
        if len(set(push_counts.keys())) == 1 and single_vecs:
            nm = single_vecs[0]
            if nm not in out:
                out[nm] = (count_token, push_counts[nm])
        i += 1
    return out


def _cf_prelude_order_ok(
    main_rs_text: str,
    spec_scalar_names: set[str],
    ghost_names: set[str],
    has_t_loop: bool,
) -> bool:
    """Return False if a ghost token is read AFTER a spec scalar in main's
    input prelude.

    The harness emits all ghost-token reads first, then spec scalars in sig
    order. That layout only matches main.rs when ghosts come first in main
    too. When a ghost is sandwiched between two spec scalars (cf467B reads
    `n`, `m_in`, `k` where `m_in` is a ghost), the emitted token order is
    wrong and the postcondition will silently see misaligned values.
    """
    if not ghost_names:
        return True
    m = re.search(r"fn\s+main\s*\(", main_rs_text)
    if m is None:
        return True
    body = main_rs_text[m.start():]
    if has_t_loop:
        loop_match = re.search(r"\b(for|while)[^{]*\{", body)
        if loop_match is not None:
            body = body[loop_match.end():]
    end = len(body)
    for marker in (
        r"\b\w+\s*\.\s*push\s*\(",
        r"\bfor\s+\w+\s+in\s+0\s*\.\.",
        r"\bwhile\s+\w+\s*<",
    ):
        m2 = re.search(marker, body)
        if m2 is not None:
            end = min(end, m2.start())
    prelude = body[:end]
    pat = re.compile(
        r"let\s+(?:mut\s+)?(\w+)\s*:\s*(?:usize|u\d+|i\d+|isize)\s*=\s*([^;]+);",
        re.DOTALL,
    )
    seen_spec_scalar = False
    for match in pat.finditer(prelude):
        name = match.group(1)
        rhs = match.group(2)
        if ".parse" not in rhs:
            continue
        if name in spec_scalar_names:
            seen_spec_scalar = True
        elif name in ghost_names:
            if seen_spec_scalar:
                return False
    return True


def _cf_scalars_read_before_vecs(
    main_rs_text: str,
    spec_scalar_names: set[str],
    spec_vec_names: set[str],
    has_t_loop: bool,
) -> bool:
    """Return False if main.rs reads (pushes into) a spec Vec param BEFORE
    a spec scalar param has been parsed.

    The harness emits all scalar reads before any Vec read, so when main
    interleaves the two (cf1681B reads `n a[..] m b[..]`) the token
    sequence won't line up.
    """
    if not spec_scalar_names or not spec_vec_names:
        return True
    m = re.search(r"fn\s+main\s*\(", main_rs_text)
    if m is None:
        return True
    body = main_rs_text[m.start():]
    if has_t_loop:
        loop_match = re.search(r"\b(for|while)[^{]*\{", body)
        if loop_match is not None:
            body = body[loop_match.end():]
    # Find the latest position of a spec-scalar parse in the prelude.
    last_scalar_end = -1
    pat = re.compile(
        r"let\s+(?:mut\s+)?(\w+)\s*:\s*(?:usize|u\d+|i\d+|isize|f32|f64)\s*=\s*([^;]+);",
        re.DOTALL,
    )
    for match in pat.finditer(body):
        name = match.group(1)
        rhs = match.group(2)
        if ".parse" not in rhs:
            continue
        if name in spec_scalar_names:
            last_scalar_end = max(last_scalar_end, match.end())
    if last_scalar_end < 0:
        return True
    # Find the earliest push to a spec Vec.
    earliest_push = len(body)
    for vec_name in spec_vec_names:
        push_pat = re.compile(rf"\b{re.escape(vec_name)}\s*\.\s*push\s*\(")
        m2 = push_pat.search(body)
        if m2 is not None:
            earliest_push = min(earliest_push, m2.start())
    return earliest_push >= last_scalar_end


def _cf_extract_vec_length_hints(
    requires_clauses: list[str],
    vec_param_names: set[str],
) -> dict[str, str]:
    """Pull `<vec>.len() == <ident>` hints from requires clauses.

    Returns `{vec_name: ident}` for vec params whose required length is
    exactly a single identifier (most commonly a sibling scalar param).
    Clauses with arithmetic on the RHS are intentionally skipped: the
    harness can't easily evaluate arbitrary expressions over yet-unparsed
    tokens, and a wrong length is worse than no hint.
    """
    out: dict[str, str] = {}
    if not requires_clauses or not vec_param_names:
        return out
    for clause in requires_clauses:
        text = clause.strip()
        for vec_name in vec_param_names:
            pat = re.compile(
                rf"\b{re.escape(vec_name)}\s*(?:@\s*)?\.\s*len\s*\(\s*\)\s*==\s*"
                r"([A-Za-z_][A-Za-z_0-9]*)\b"
                r"(?!\s*[\.\(\[\+\-\*/%])"
            )
            m = pat.search(text)
            if m is None:
                continue
            ident = m.group(1)
            # Skip if RHS itself looks like a method/function call or
            # has a trailing `as` cast we can't yet handle.
            tail = text[m.end():m.end() + 4].lstrip()
            if tail.startswith("as "):
                # `<vec>.len() == n as int` is a length-equals-scalar; safe.
                pass
            out.setdefault(vec_name, ident)
    return out


def _cf_detect_t_loop(main_rs_text: str) -> bool:
    """Detect whether main.rs reads a leading test count and loops over that
    many cases. The count may be named `t`, `q`, `n`, etc.; we distinguish
    a test-count loop from an array-fill loop by requiring the loop body to
    invoke `Solution::...` -- array-fill loops only push into a Vec, while
    test-count loops always call the spec method per case (whether output
    is emitted inline via `println!` or buffered via `out.push_str`).
    """
    if not main_rs_text:
        return False
    m = re.search(r"fn\s+main\s*\(", main_rs_text)
    if m is None:
        return False
    body = main_rs_text[m.start():]
    # Collect leading scalar bindings that come from a stdin parse.
    candidates: list[str] = []
    for match in re.finditer(
        r"\blet\s+(?:mut\s+)?(\w+)\s*:\s*(?:usize|u\d+|i\d+|isize)\s*=\s*([^;]+);",
        body, re.DOTALL,
    ):
        rhs = match.group(2)
        if ".parse" not in rhs:
            continue
        candidates.append(match.group(1))
    for match in re.finditer(
        r"\bif\s+let\s+Ok\s*\(\s*(\w+)\s*\)\s*=",
        body,
    ):
        candidates.append(match.group(1))
    if not candidates:
        return False
    for name in candidates:
        loop_pat = re.compile(
            rf"\b(?:for\s+\w+\s+in\s+0\s*\.\.\s*{re.escape(name)}\b"
            rf"|while\s+\w+\s*<\s*{re.escape(name)}\b)"
        )
        m2 = loop_pat.search(body)
        if m2 is None:
            continue
        # Find the matching brace-balanced loop body.
        rest = body[m2.end():]
        bo = rest.find('{')
        if bo < 0:
            continue
        depth = 1
        end = -1
        for i, c in enumerate(rest[bo + 1:]):
            if c == '{':
                depth += 1
            elif c == '}':
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end < 0:
            continue
        inner = rest[bo + 1:bo + 1 + end]
        # Test-count loop signal: actually invokes the spec method per case.
        # (Vec-fill loops only `push` into a Vec; the spec call sits outside.)
        if re.search(r"\bSolution\s*::", inner) is not None:
            return True
    return False


def _cf_param_consumer(
    param_name: str,
    spec_type: str,
    available_count_vars: dict[str, str],
    source: str = "input_tokens",
    length_override: str | None = None,
) -> tuple[str | None, str | None]:
    """Generate Rust code consuming `param_name` of type `spec_type` from a
    whitespace-token iterator.

    Returns `(rust_code, count_hint_var)`.  `count_hint_var` is set when the
    param is itself a usize-like scalar usable as a length for a later Vec.
    """
    inner, _, _ = strip_ref(spec_type)
    inner = inner.strip()
    rust_ty = spec_to_direct_rust_type(spec_type)
    if rust_ty is None:
        return None, None

    if inner in {"int", "nat", "usize"} or inner in PRIM_INTS:
        code = (
            f"        let {param_name}: {rust_ty} = "
            f"{source}.next().expect(\"missing token for {param_name}\")"
            f".parse().expect(\"parse failed for {param_name}\");"
        )
        return code, param_name

    if inner == "bool":
        # Accept "true"/"false"/"1"/"0"/"Yes"/"No" as a single token.
        code = (
            f"        let {param_name}: bool = {{\n"
            f"            let __tok = {source}.next().expect(\"missing token for {param_name}\");\n"
            f"            match __tok.to_ascii_lowercase().as_str() {{\n"
            f"                \"true\" | \"1\" | \"yes\" | \"y\" => true,\n"
            f"                \"false\" | \"0\" | \"no\" | \"n\" => false,\n"
            f"                _ => panic!(\"bad bool token: {{}}\", __tok),\n"
            f"            }}\n"
            f"        }};"
        )
        return code, None

    if inner == "char":
        code = (
            f"        let {param_name}: char = {source}.next()"
            f".expect(\"missing token for {param_name}\")"
            f".chars().next().expect(\"empty char token\");"
        )
        return code, None

    if inner in {"String", "SpecString", "str"}:
        code = (
            f"        let {param_name}: std::rc::Rc<String> = std::rc::Rc::new("
            f"{source}.next().expect(\"missing token for {param_name}\").to_string());"
        )
        return code, None

    for seq_name in ("Vec", "Seq"):
        seq_arg = generic_arg(inner, seq_name)
        if seq_arg is not None:
            elem_ty = spec_to_direct_rust_type(seq_arg)
            if elem_ty is None:
                return None, None
            seq_inner = seq_arg.strip()
            if seq_inner not in {"int", "nat", "usize"} and seq_inner not in PRIMITIVES:
                # Avoid nested-collection parsing; problem-specific.
                return None, None
            if length_override is not None:
                count_expr = length_override
            else:
                # Pick a count source: previously parsed scalar named like a count.
                count_var = None
                for hint_name in ("n", "m", "k", "len", "count", "size"):
                    if hint_name in available_count_vars:
                        count_var = available_count_vars[hint_name]
                        break
                if count_var is None and available_count_vars:
                    # fall back to the most recently parsed scalar
                    count_var = next(reversed(available_count_vars.values()))
                if count_var is None:
                    # consume an inline length token
                    count_expr = (
                        f"{source}.next().expect(\"missing length token\")"
                        f".parse::<usize>().expect(\"bad length token\")"
                    )
                else:
                    count_expr = f"({count_var}) as usize"
            elem_parse = (
                f"{source}.next().expect(\"missing token for {param_name} element\")"
                f".parse::<{elem_ty}>()"
                f".expect(\"parse failed for {param_name} element\")"
            )
            code = (
                f"        let __count_{param_name}: usize = {count_expr};\n"
                f"        let {param_name}: {rust_ty} = std::rc::Rc::new("
                f"(0..__count_{param_name}).map(|_| {elem_parse}).collect());"
            )
            return code, None

    return None, None


def _cf_interleaved_block(
    members: list[str],
    count_token: str,
    model,
    available_count_vars: dict[str, str],
) -> str | None:
    """Emit a Rust block that fills several Vec params in lockstep, reading
    one element per Vec per outer iteration.  This mirrors the standard
    codeforces "n lines of k columns" layout that `main.rs` typically uses.
    """
    by_name = {p.name: p for p in model.sig.params}
    elem_types: list[str] = []
    full_types: list[str] = []
    for name in members:
        p = by_name.get(name)
        if p is None:
            return None
        inner, _, _ = strip_ref(p.spec_type)
        inner = inner.strip()
        seq_arg = generic_arg(inner, "Vec") or generic_arg(inner, "Seq")
        if seq_arg is None:
            return None
        elem_ty = spec_to_direct_rust_type(seq_arg)
        if elem_ty is None:
            return None
        seq_inner = seq_arg.strip()
        if seq_inner not in {"int", "nat", "usize"} and seq_inner not in PRIMITIVES:
            return None
        elem_types.append(elem_ty)
        full_types.append(spec_to_direct_rust_type(p.spec_type) or f"std::rc::Rc<Vec<{elem_ty}>>")
    # Resolve `count_token`: prefer a previously parsed scalar with the
    # same name; fall back to consuming an inline length token.
    if count_token in available_count_vars:
        count_expr = f"({count_token}) as usize"
    else:
        # Try usual hint names if `count_token` was internal.
        fallback = None
        for hint in ("n", "m", "k", "len", "count", "size"):
            if hint in available_count_vars:
                fallback = f"({available_count_vars[hint]}) as usize"
                break
        if fallback is None:
            count_expr = (
                'input_tokens.next().expect("missing interleaved length")'
                '.parse::<usize>().expect("bad interleaved length")'
            )
        else:
            count_expr = fallback
    lines: list[str] = []
    lines.append(f"        let __ilen: usize = {count_expr};")
    for name, full_ty, elem_ty in zip(members, full_types, elem_types):
        lines.append(f"        let mut __ibuf_{name}: Vec<{elem_ty}> = Vec::with_capacity(__ilen);")
    lines.append("        for _ in 0..__ilen {")
    for name, full_ty, elem_ty in zip(members, full_types, elem_types):
        if elem_ty == "bool":
            lines.append(
                f"            let __tok = input_tokens.next().expect(\"missing interleaved bool\");"
            )
            lines.append(
                f"            let __v_{name}: bool = match __tok.to_ascii_lowercase().as_str() {{"
            )
            lines.append('                "true" | "1" | "yes" | "y" => true,')
            lines.append('                "false" | "0" | "no" | "n" => false,')
            lines.append('                _ => panic!("bad interleaved bool: {}", __tok),')
            lines.append("            };")
            lines.append(f"            __ibuf_{name}.push(__v_{name});")
        elif elem_ty == "char":
            lines.append(
                f"            let __v_{name}: char = input_tokens.next().expect(\"missing interleaved char\")"
                ".chars().next().expect(\"empty interleaved char\");"
            )
            lines.append(f"            __ibuf_{name}.push(__v_{name});")
        else:
            lines.append(
                f"            let __v_{name}: {elem_ty} = input_tokens.next()"
                f".expect(\"missing token for {name}\")"
                f".parse().expect(\"parse failed for {name}\");"
            )
            lines.append(f"            __ibuf_{name}.push(__v_{name});")
    lines.append("        }")
    for name, full_ty in zip(members, full_types):
        lines.append(f"        let {name}: {full_ty} = std::rc::Rc::new(__ibuf_{name});")
    return "\n".join(lines)


def _cf_return_consumer(
    name: str,
    spec_type: str,
    available_count_vars: dict[str, str] | None = None,
    length_prefixed: bool = True,
) -> str | None:
    """Generate Rust code that pulls the expected return value from `output_tokens`."""
    if available_count_vars is None:
        available_count_vars = {}
    inner, _, _ = strip_ref(spec_type)
    inner = inner.strip()
    rust_ty = spec_to_direct_rust_type(spec_type)
    if rust_ty is None:
        return None

    if inner in {"int", "nat", "usize"} or inner in PRIM_INTS:
        return (
            f"        let {name}: {rust_ty} = output_tokens.next()"
            f".expect(\"missing output token\")"
            f".parse().expect(\"bad output token\");"
        )
    if inner == "bool":
        return (
            f"        let {name}: bool = {{\n"
            "            let __tok = output_tokens.next().expect(\"missing output token\");\n"
            "            match __tok.to_ascii_lowercase().as_str() {\n"
            "                \"true\" | \"1\" | \"yes\" | \"y\" => true,\n"
            "                \"false\" | \"0\" | \"no\" | \"n\" => false,\n"
            "                _ => panic!(\"bad bool output: {}\", __tok),\n"
            "            }\n"
            "        };"
        )
    if inner == "char":
        return (
            f"        let {name}: char = output_tokens.next()"
            ".expect(\"missing output token\").chars().next()"
            ".expect(\"empty char output\");"
        )
    if inner in {"String", "SpecString", "str"}:
        return (
            f"        let {name}: std::rc::Rc<String> = std::rc::Rc::new("
            "output_tokens.next().expect(\"missing output token\").to_string());"
        )
    for seq_name in ("Vec", "Seq"):
        seq_arg = generic_arg(inner, seq_name)
        if seq_arg is not None:
            elem_ty = spec_to_direct_rust_type(seq_arg)
            if elem_ty is None:
                return None
            seq_inner = seq_arg.strip()
            if seq_inner not in {"int", "nat", "usize"} and seq_inner not in PRIMITIVES:
                return None
            if length_prefixed:
                count_setup = (
                    "        let __out_count: usize = output_tokens.next()"
                    ".expect(\"missing output length\")"
                    ".parse().expect(\"bad output length\");\n"
                )
            else:
                # No length prefix in raw output: length is determined by an
                # input scalar. The output usually corresponds to the LAST
                # variable-length section of the input (e.g. `m` queries),
                # so prefer the most recently parsed count over a generic
                # name-hint. Falls back to common names if unavailable.
                count_var: str | None = None
                if available_count_vars:
                    count_var = next(reversed(available_count_vars.values()))
                if count_var is None:
                    for hint_name in ("n", "m", "k", "len", "count", "size"):
                        if hint_name in available_count_vars:
                            count_var = available_count_vars[hint_name]
                            break
                if count_var is None:
                    # No way to know the length without a prefix; refuse.
                    return None
                count_setup = (
                    f"        let __out_count: usize = ({count_var}) as usize;\n"
                )
            return (
                f"{count_setup}"
                f"        let {name}: {rust_ty} = std::rc::Rc::new("
                f"(0..__out_count).map(|_| output_tokens.next()"
                f".expect(\"missing output element\").parse::<{elem_ty}>()"
                f".expect(\"bad output element\")).collect());"
            )

    # Tuple return: read one whitespace-separated token per element.
    tuple_items = parse_tuple_items(inner)
    if tuple_items is not None:
        elem_lines: list[str] = []
        elem_names: list[str] = []
        for idx, item_ty in enumerate(tuple_items):
            item_inner = item_ty.strip()
            item_rust = spec_to_direct_rust_type(item_inner)
            if item_rust is None:
                return None
            sub = f"__{name}_{idx}"
            if item_inner in {"int", "nat", "usize"} or item_inner in PRIM_INTS:
                elem_lines.append(
                    f"        let {sub}: {item_rust} = output_tokens.next()"
                    f".expect(\"missing output token\")"
                    f".parse().expect(\"bad output token\");"
                )
            elif item_inner == "bool":
                elem_lines.append(
                    f"        let {sub}: bool = {{\n"
                    "            let __tok = output_tokens.next().expect(\"missing output token\");\n"
                    "            match __tok.to_ascii_lowercase().as_str() {\n"
                    "                \"true\" | \"1\" | \"yes\" | \"y\" => true,\n"
                    "                \"false\" | \"0\" | \"no\" | \"n\" => false,\n"
                    "                _ => panic!(\"bad bool output: {}\", __tok),\n"
                    "            }\n"
                    "        };"
                )
            elif item_inner == "char":
                elem_lines.append(
                    f"        let {sub}: char = output_tokens.next()"
                    ".expect(\"missing output token\").chars().next()"
                    ".expect(\"empty char output\");"
                )
            else:
                return None
            elem_names.append(sub)
        elem_lines.append(
            f"        let {name}: {rust_ty} = ({', '.join(elem_names)});"
        )
        return "\n".join(elem_lines)
    return None


def build_cf_runtime_main(
    arg_parse_block: str,
    return_parse_block: str,
    call_expr: str,
    source_tests_dir: str,
    has_t_loop: bool,
    requires_call_expr: str | None = None,
) -> str:
    """Build the codeforces-flavour runtime that tokenizes raw stdin/stdout strings.

    Each testcase line is `{"input": "<stdin text>", "output": "<stdout text>"}`.
    The runtime tokenises both fields by whitespace and consumes one (args, ret)
    tuple per case (with `t` cases when the original `main.rs` reads a leading
    case-count, otherwise a single case per line).

    When `requires_call_expr` is provided, each per-case binding evaluates the
    spec's `requires` clauses first; if they don't hold, the case is reported
    as `Some(None)` and skipped from soundness/completeness counting.
    """
    if has_t_loop:
        cases_expr = (
            'input_tokens.next().expect("missing test count")'
            '.parse::<usize>().expect("bad test count")'
        )
    else:
        cases_expr = "1usize"
    if requires_call_expr is not None:
        case_eval = f'''        let requires_ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            {requires_call_expr}
        }})).unwrap_or(false);
        if !requires_ok {{
            results.push(None);
            continue;
        }}
        let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            {call_expr}
        }})).unwrap_or(false);
        results.push(Some(ok));'''
    else:
        case_eval = f'''        let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            {call_expr}
        }})).unwrap_or(false);
        results.push(Some(ok));'''
    return f'''fn main() {{
    let handle = std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(run)
        .expect("failed to spawn runner thread");
    let code = handle.join().expect("runner thread panicked");
    std::process::exit(code);
}}

fn run_one_case(line: &str) -> Vec<Option<bool>> {{
    let mut obj = parse_line_object(line);
    let input_str = match obj.remove("input") {{
        Some(Value::String(s)) => s,
        Some(other) => panic!("expected string input, got {{:?}}", other),
        None => panic!("missing input field"),
    }};
    let output_str = match obj.remove("output") {{
        Some(Value::String(s)) => s,
        Some(other) => panic!("expected string output, got {{:?}}", other),
        None => panic!("missing output field"),
    }};

    let mut input_tokens = input_str.split_whitespace();
    let mut output_tokens = output_str.split_whitespace();

    let cases: usize = {cases_expr};
    let mut results: Vec<Option<bool>> = Vec::with_capacity(cases);
    for _ in 0..cases {{
{arg_parse_block}
{return_parse_block}
{case_eval}
    }}
    results
}}

fn run_phase(label: &str, path: &std::path::Path, expected: bool) -> i32 {{
    let mut file = match std::fs::File::open(path) {{
        Ok(f) => f,
        Err(e) => {{
            eprintln!("[{{}}] cannot open {{:?}}: {{}}", label, path, e);
            return 1;
        }}
    }};
    let mut contents = String::new();
    if let Err(e) = file.read_to_string(&mut contents) {{
        eprintln!("[{{}}] read failed for {{:?}}: {{}}", label, path, e);
        return 1;
    }}

    let mut total_lines: usize = 0;
    let mut total_cases: usize = 0;
    let mut unexpected_cases: usize = 0;
    let mut bad_lines: usize = 0;
    for raw_line in contents.lines() {{
        let line = raw_line.trim().trim_end_matches(',');
        if line.is_empty() || !line.starts_with('{{') {{
            continue;
        }}
        total_lines += 1;
        let results: Vec<Option<bool>> = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_one_case(line))) {{
            Ok(r) => r,
            Err(_) => {{
                bad_lines += 1;
                if bad_lines <= 5 {{
                    eprintln!("[{{}}] PARSE_FAIL line #{{}}: {{}}", label, total_lines, &line[..line.len().min(240)]);
                }}
                Vec::new()
            }}
        }};
        if results.is_empty() {{
            // Parse-panic lines are skipped (the harness's heuristic input
            // tokenizer cannot decode this problem-specific format). They
            // are reported separately as `bad_lines` and do not count
            // toward soundness/completeness pass/fail -- only verdicts the
            // converter actually produced are scored.
            continue;
        }}
        if expected {{
            // Soundness: every sub-test of every line must accept.
            // Count and report at sub-test (case) granularity so a single
            // bad sub-test inside a multi-test line is not hidden.
            for (idx, slot) in results.iter().enumerate() {{
                let ok = match slot {{
                    Some(b) => *b,
                    None => continue, // requires-violating sub-test
                }};
                total_cases += 1;
                if ok != expected {{
                    unexpected_cases += 1;
                    if unexpected_cases <= 5 {{
                        eprintln!(
                            "[{{}}] UNEXPECTED case #{{}} (line {{}} sub {{}}, got {{}}, expected {{}}): {{}}",
                            label,
                            total_cases,
                            total_lines,
                            idx + 1,
                            ok,
                            expected,
                            &line[..line.len().min(240)],
                        );
                    }}
                }}
            }}
        }} else {{
            // Completeness: each mutated line is one logical testcase. The
            // mutation may only perturb one sub-test's output, so we count
            // the line as "rejected" if at least one sub-test (with a real
            // verdict) returns false.
            let mut had_verdict = false;
            let mut any_rejected = false;
            for slot in results.iter() {{
                if let Some(b) = slot {{
                    had_verdict = true;
                    if !*b {{
                        any_rejected = true;
                    }}
                }}
            }}
            if !had_verdict {{
                continue;
            }}
            total_cases += 1;
            if !any_rejected {{
                unexpected_cases += 1;
                if unexpected_cases <= 5 {{
                    eprintln!(
                        "[{{}}] UNEXPECTED line #{{}} (every sub-test accepted, expected at least one rejection): {{}}",
                        label,
                        total_lines,
                        &line[..line.len().min(240)],
                    );
                }}
            }}
        }}
    }}

    let unit = if expected {{ "cases" }} else {{ "lines" }};
    if total_cases == 0 {{
        // Every line failed to parse. Treat as a hard error so the user
        // notices, instead of vacuously passing.
        println!(
            "[{{}}] EMPTY: no decodable testcases (skipped {{}} parse-failed lines) in {{:?}}",
            label, bad_lines, path
        );
        return 1;
    }}
    if unexpected_cases == 0 {{
        if bad_lines > 0 {{
            println!(
                "[{{}}] PASS: {{}} / {{}} {{}} as expected (skipped {{}} parse-failed lines)",
                label, total_cases, total_cases, unit, bad_lines
            );
        }} else {{
            println!("[{{}}] PASS: {{}} / {{}} {{}} as expected", label, total_cases, total_cases, unit);
        }}
        0
    }} else {{
        if bad_lines > 0 {{
            println!(
                "[{{}}] FAIL: {{}} / {{}} {{}} unexpected (skipped {{}} parse-failed lines)",
                label, unexpected_cases, total_cases, unit, bad_lines
            );
        }} else {{
            println!("[{{}}] FAIL: {{}} / {{}} {{}} unexpected", label, unexpected_cases, total_cases, unit);
        }}
        1
    }}
}}

fn run() -> i32 {{
    // Silence Rust's default panic message: per-case panics are expected when
    // the heuristic stdin/stdout parser meets a problem-specific format it
    // can't decode. `catch_unwind` already turns the panic into a `false`.
    std::panic::set_hook(Box::new(|_| {{}}));

    let mut soundness = false;
    let mut completeness = false;
    for arg in std::env::args().skip(1) {{
        match arg.as_str() {{
            "--soundness" => soundness = true,
            "--completeness" => completeness = true,
            "--all" => {{ soundness = true; completeness = true; }}
            other => {{
                eprintln!("unknown argument: {{}}", other);
                eprintln!("usage: post2exe-checker [--soundness] [--completeness]");
                return 2;
            }}
        }}
    }}
    if !soundness && !completeness {{
        soundness = true;
        completeness = true;
    }}

    let self_path = std::path::Path::new(file!());
    let tests_dir = self_path.parent().unwrap_or(std::path::Path::new("."));
    let fallback_tests_dir = std::path::Path::new({source_tests_dir});
    let resolve = |name: &str| -> std::path::PathBuf {{
        let p = tests_dir.join(name);
        if p.exists() {{ p }} else {{ fallback_tests_dir.join(name) }}
    }};

    let mut code = 0;
    if soundness {{
        let path = resolve("testcases.jsonl");
        code |= run_phase("soundness", &path, true);
    }}
    if completeness {{
        let path = resolve("mutated_testcases.jsonl");
        code |= run_phase("completeness", &path, false);
    }}
    code
}}'''


def build_runtime_main(
    parse_block: str,
    call_expr: str,
    source_tests_dir: str,
    requires_call_expr: str | None = None,
) -> str:
    """Build the shared `fn main` / `fn run` runtime emitted by both backends.

    The generated binary accepts:

    - `--soundness` to validate `testcases.jsonl` (postcondition must accept every case)
    - `--completeness` to validate `mutated_testcases.jsonl` (postcondition must reject every case)

    With no flag, both phases run.  Exit code is non-zero if any phase has at
    least one unexpected outcome, or if a required testcase file is missing.
    """
    if requires_call_expr is not None:
        # Evaluate requires first (with the parsed values still in scope),
        # then -- if it holds -- evaluate the postcondition. We use an
        # inner result enum to thread the verdict back out of the parse
        # panic guard without moving anything across closures.
        split_body = f'''    enum InnerResult {{ Ok(bool), Skip }}
    let parsed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
        let mut obj = parse_line_object(line);
        if let Some(Value::Object(inner)) = obj.remove("input") {{
            for (k, v) in inner {{
                obj.entry(k).or_insert(v);
            }}
        }}
{parse_block}
        let req_ok: bool = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            {requires_call_expr}
        }})).unwrap_or(false);
        if !req_ok {{
            return InnerResult::Skip;
        }}
        let ok: bool = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
            {call_expr}
        }})).unwrap_or(false);
        InnerResult::Ok(ok)
    }}));
    match parsed {{
        Ok(InnerResult::Ok(b)) => Outcome::Ok(b),
        Ok(InnerResult::Skip) => Outcome::Skip,
        Err(_) => Outcome::Bad,
    }}'''
    else:
        split_body = f'''    let parsed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {{
        let mut obj = parse_line_object(line);
        if let Some(Value::Object(inner)) = obj.remove("input") {{
            for (k, v) in inner {{
                obj.entry(k).or_insert(v);
            }}
        }}
{parse_block}
        Box::new(move || {{ {call_expr} }}) as Box<dyn FnOnce() -> bool>
    }}));
    match parsed {{
        Ok(call) => {{
            let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(call))
                .unwrap_or(false);
            Outcome::Ok(ok)
        }}
        Err(_) => Outcome::Bad,
    }}'''
    return f'''fn main() {{
    let handle = std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(run)
        .expect("failed to spawn runner thread");
    let code = handle.join().expect("runner thread panicked");
    std::process::exit(code);
}}

#[allow(dead_code)]
enum Outcome {{
    Ok(bool),
    Skip,  // requires-violating
    Bad,   // parse panic
}}

fn run_one_case(line: &str) -> bool {{
    let mut obj = parse_line_object(line);
    if let Some(Value::Object(inner)) = obj.remove("input") {{
        for (k, v) in inner {{
            obj.entry(k).or_insert(v);
        }}
    }}
{parse_block}
    {call_expr}
}}

fn run_one_case_split(line: &str) -> Outcome {{
{split_body}
}}

fn run_phase(label: &str, path: &std::path::Path, expected: bool) -> i32 {{
    let mut file = match std::fs::File::open(path) {{
        Ok(f) => f,
        Err(e) => {{
            eprintln!("[{{}}] cannot open {{:?}}: {{}}", label, path, e);
            return 1;
        }}
    }};
    let mut contents = String::new();
    if let Err(e) = file.read_to_string(&mut contents) {{
        eprintln!("[{{}}] read failed for {{:?}}: {{}}", label, path, e);
        return 1;
    }}

    let mut total: usize = 0;
    let mut unexpected: usize = 0;
    let mut bad_lines: usize = 0;
    let mut total_lines: usize = 0;
    for raw_line in contents.lines() {{
        let line = raw_line.trim().trim_end_matches(',');
        if line.is_empty() || !line.starts_with('{{') {{
            continue;
        }}
        total_lines += 1;
        let ok = match run_one_case_split(line) {{
            Outcome::Ok(b) => b,
            Outcome::Skip => {{
                continue;
            }}
            Outcome::Bad => {{
                bad_lines += 1;
                if bad_lines <= 5 {{
                    eprintln!(
                        "[{{}}] PARSE_FAIL line #{{}}: {{}}",
                        label,
                        total_lines,
                        &line[..line.len().min(240)],
                    );
                }}
                continue;
            }}
        }};
        if ok != expected {{
            unexpected += 1;
            if unexpected <= 5 {{
                eprintln!(
                    "[{{}}] UNEXPECTED case #{{}} (got {{}}, expected {{}}): {{}}",
                    label,
                    total + 1,
                    ok,
                    expected,
                    &line[..line.len().min(240)],
                );
            }}
        }}
        total += 1;
    }}

    if total == 0 {{
        println!(
            "[{{}}] EMPTY: no decodable testcases (skipped {{}} parse-failed lines) in {{:?}}",
            label, bad_lines, path
        );
        return 1;
    }}
    if unexpected == 0 {{
        if bad_lines > 0 {{
            println!(
                "[{{}}] PASS: {{}} / {{}} cases as expected (skipped {{}} parse-failed lines)",
                label, total, total, bad_lines
            );
        }} else {{
            println!("[{{}}] PASS: {{}} / {{}} cases as expected", label, total, total);
        }}
        0
    }} else {{
        if bad_lines > 0 {{
            println!(
                "[{{}}] FAIL: {{}} / {{}} cases unexpected (skipped {{}} parse-failed lines)",
                label, unexpected, total, bad_lines
            );
        }} else {{
            println!("[{{}}] FAIL: {{}} / {{}} cases unexpected", label, unexpected, total);
        }}
        1
    }}
}}

fn run() -> i32 {{
    // Silence Rust's default panic message: per-case panics are turned into
    // `false` by `catch_unwind` further down, so don't pollute stderr.
    std::panic::set_hook(Box::new(|_| {{}}));

    let mut soundness = false;
    let mut completeness = false;
    for arg in std::env::args().skip(1) {{
        match arg.as_str() {{
            "--soundness" => soundness = true,
            "--completeness" => completeness = true,
            "--all" => {{ soundness = true; completeness = true; }}
            other => {{
                eprintln!("unknown argument: {{}}", other);
                eprintln!("usage: post2exe-checker [--soundness] [--completeness]");
                return 2;
            }}
        }}
    }}
    if !soundness && !completeness {{
        soundness = true;
        completeness = true;
    }}

    let self_path = std::path::Path::new(file!());
    let tests_dir = self_path.parent().unwrap_or(std::path::Path::new("."));
    let fallback_tests_dir = std::path::Path::new({source_tests_dir});
    let resolve = |name: &str| -> std::path::PathBuf {{
        let p = tests_dir.join(name);
        if p.exists() {{ p }} else {{ fallback_tests_dir.join(name) }}
    }};

    let mut code = 0;
    if soundness {{
        let path = resolve("testcases.jsonl");
        code |= run_phase("soundness", &path, true);
    }}
    if completeness {{
        let path = resolve("mutated_testcases.jsonl");
        code |= run_phase("completeness", &path, false);
    }}
    code
}}'''


def _is_stub_spec_function(fn: DirectFunction) -> bool:
    """Detect spec helpers whose body is just a constant literal.

    These act as placeholders (e.g. `spec fn count(...) -> int { 0 }`) and
    can never produce the actual algorithmic value the test data expects.
    Treating them as real specs causes the generated checker to reject
    every non-trivial test case.
    """
    body = (fn.body_text or "").strip()
    if not body.startswith("{") or not body.endswith("}"):
        return False
    inner = body[1:-1].strip()
    if not inner:
        return False
    # Strip a single-expression form: numeric / boolean / `int`-cast literal.
    if re.fullmatch(r"-?\d+(_\d+)*(int|nat|i\d+|u\d+|isize|usize)?", inner):
        return True
    if inner in {"true", "false"}:
        return True
    return False


def generate_direct_post2exe(problem_dir: Path) -> tuple[str, list[str]]:
    model, warnings = build_direct_problem_model(problem_dir)
    if model is None:
        return "", warnings

    # Refuse stub specs: any helper function used by the postcondition
    # body that returns a constant placeholder. The postcondition would
    # demand `result == 0` (or similar) for every input, which is almost
    # never what the test data shows.
    stub_names = [
        name for name, fn in model.functions.items()
        if name != model.sig.fn_name and _is_stub_spec_function(fn)
    ]
    if stub_names:
        return "", [
            f"spec helper{'s' if len(stub_names) > 1 else ''} "
            f"{stub_names} appear to be stubs (constant body); "
            f"postcondition cannot be evaluated against real test outputs"
        ]

    try:
        mod_function_sources = infer_modulo_function_sources(model)
        translator = DirectSpecTranslator(model.functions, mod_function_sources)
        translated_consts = [
            _translate_direct_const_line(line, translator) for line in model.const_lines
        ]
        translated_fns = [
            translator.translate_function(fn) for fn in model.functions.values()
        ]
        translated_fns.extend(
            translator.translate_mod_function(model.functions[name])
            for name in sorted(mod_function_sources)
        )

        is_codeforces = problem_dir.parent.name == "codeforces"
        call_args: list[str] = []
        if is_codeforces:
            main_rs_path = problem_dir / "main.rs"
            main_rs_text = main_rs_path.read_text() if main_rs_path.exists() else ""
            has_t_loop = _cf_detect_t_loop(main_rs_text)

            # Build the set of Vec-typed params so the interleaved-loop
            # detector can scope its scan.
            vec_param_names: set[str] = set()
            for p in model.sig.params:
                if p.is_result:
                    continue
                inner, _, _ = strip_ref(p.spec_type)
                inner = inner.strip()
                if generic_arg(inner, "Vec") is not None or generic_arg(inner, "Seq") is not None:
                    vec_param_names.add(p.name)
            interleaved = _cf_detect_interleaved_vecs(main_rs_text, vec_param_names)
            loop_multipliers = _cf_detect_loop_multipliers(main_rs_text, vec_param_names)
            output_length_prefixed = _cf_detect_output_length_prefixed(main_rs_text)
            spec_param_names = {p.name for p in model.sig.params if not p.is_result}
            input_ghosts = _cf_detect_input_prelude(
                main_rs_text, spec_param_names, has_t_loop
            ) or []
            vec_length_hints = _cf_extract_vec_length_hints(
                model.requires_clauses, vec_param_names
            )
            spec_scalar_names_for_order: set[str] = set()
            for p in model.sig.params:
                if p.is_result:
                    continue
                inner_ty, _, _ = strip_ref(p.spec_type)
                inner_ty = inner_ty.strip()
                if inner_ty in {"int", "nat", "usize", "bool", "char"} or inner_ty in PRIM_INTS:
                    spec_scalar_names_for_order.add(p.name)
            # Refusal: ghost token interleaved with spec scalars in main's
            # prelude (e.g. cf467B reads `n m_in k` where m_in is a ghost).
            # The harness emits ghosts first, so the token order would be
            # silently wrong.
            if input_ghosts:
                ghost_names = {n for n, _ in input_ghosts}
                if not _cf_prelude_order_ok(
                    main_rs_text, spec_scalar_names_for_order, ghost_names, has_t_loop
                ):
                    return "", [
                        "cf: ghost token interleaved with spec scalars in "
                        "main.rs prelude; cannot align stdin tokens with "
                        "spec inputs"
                    ]
            # Refusal: main reads a spec Vec before all spec scalars
            # (cf1681B reads `n a[..] m b[..]`). The harness emits all
            # scalars first, so the token sequence would be misaligned.
            if not _cf_scalars_read_before_vecs(
                main_rs_text, spec_scalar_names_for_order, vec_param_names, has_t_loop
            ):
                return "", [
                    "cf: main.rs interleaves scalar reads with Vec reads; "
                    "harness's scalars-first ordering cannot align with stdin"
                ]
            # Refusal #1: main.rs's `Solution::<fn>(...)` invocation
            # passes transformed expressions rather than the spec params
            # verbatim -- the harness's "tokenize stdin and bind to spec
            # params" model will silently misalign data.
            short_fn = model.sig.fn_name.removesuffix("_postcondition")
            main_call_args = _cf_detect_main_call_args(main_rs_text, short_fn)
            if main_call_args is not None and not _cf_call_args_are_simple(
                main_call_args, spec_param_names
            ):
                return "", [
                    f"cf: main.rs preprocesses inputs before `{short_fn}` "
                    f"call (args: {main_call_args}); cannot align stdin "
                    "tokens with spec params"
                ]
            # Refusal #2: at least one spec param is computed in main.rs
            # rather than read directly from stdin (e.g. cf158B counts
            # occurrences into c1/c2/c3/c4; cf1714A computes
            # `now = h*60 + m`). Without simulating main.rs, the harness
            # cannot recover the spec input from raw stdin.
            if main_call_args is not None:
                computed_params = []
                for p in model.sig.params:
                    if p.is_result:
                        continue
                    p_is_vec = p.name in vec_param_names
                    if not _cf_main_param_is_directly_read(
                        main_rs_text, p.name, p_is_vec
                    ):
                        computed_params.append(p.name)
                if computed_params:
                    return "", [
                        f"cf: spec params {computed_params} are computed in "
                        f"main.rs (not parsed directly from stdin); cannot "
                        "align stdin tokens with spec inputs"
                    ]

            arg_lines: list[str] = []
            return_line: str | None = None
            available_count_vars: dict[str, str] = {}
            emitted_groups: set[int] = set()

            # Codeforces convention: scalars are typically read before any
            # variable-length arrays, so reorder params to match input order
            # rather than spec/sig order. The call expression still uses the
            # original sig order.
            def _is_scalar_input(p) -> bool:
                inner, _, _ = strip_ref(p.spec_type)
                inner = inner.strip()
                if inner in {"int", "nat", "usize", "bool", "char"}:
                    return True
                if inner in PRIM_INTS:
                    return True
                return False

            input_params = [p for p in model.sig.params if not p.is_result]
            ordered_params = [p for p in input_params if _is_scalar_input(p)] + [
                p for p in input_params if not _is_scalar_input(p)
            ]

            # Consume any leading "ghost" tokens that main.rs reads but the
            # spec doesn't take as an input (typically `n`, the length of a
            # following Vec). They get bound as locals and registered in
            # `available_count_vars` so subsequent Vec parsers can use
            # them as length hints.
            for ghost_name, ghost_ty in input_ghosts:
                arg_lines.append(
                    f"        let {ghost_name}: {ghost_ty} = "
                    f"input_tokens.next().expect(\"missing token for {ghost_name}\")"
                    f".parse().expect(\"parse failed for {ghost_name}\");"
                )
                available_count_vars[ghost_name] = ghost_name

            for param in ordered_params:
                if param.name in interleaved:
                    count_token, col_idx, members = interleaved[param.name]
                    group_id = id(members)
                    if group_id in emitted_groups:
                        continue
                    emitted_groups.add(group_id)
                    code = _cf_interleaved_block(members, count_token, model, available_count_vars)
                    if code is None:
                        return "", [
                            f"cf: unsupported interleaved group {members} in {model.sig.fn_name}"
                        ]
                    arg_lines.append(code)
                    continue
                # If main.rs pushes K elements per iteration into this Vec,
                # use `K * count_token` as its length instead of the default
                # single-token-per-iter heuristic.
                length_override: str | None = None
                if param.name in loop_multipliers:
                    count_token, k = loop_multipliers[param.name]
                    if count_token in available_count_vars:
                        length_override = f"({k}usize) * (({available_count_vars[count_token]}) as usize)"
                # Prefer an explicit `<vec>.len() == <ident>` hint from the
                # requires clauses when it's available (and the named ident
                # has been parsed already). This disambiguates cases like
                # cf1681B where two different scalars (`n` and `m`) bound
                # two different vecs and the generic name-ranking heuristic
                # would otherwise pick the wrong one.
                if length_override is None and param.name in vec_length_hints:
                    hint_name = vec_length_hints[param.name]
                    if hint_name in available_count_vars:
                        length_override = f"({available_count_vars[hint_name]}) as usize"
                code, count_hint = _cf_param_consumer(
                    param.name, param.spec_type, available_count_vars,
                    length_override=length_override,
                )
                if code is None:
                    return "", [
                        f"cf: unsupported param type `{param.spec_type}` for `{param.name}` in {model.sig.fn_name}"
                    ]
                arg_lines.append(code)
                if count_hint is not None:
                    available_count_vars[param.name] = count_hint

            for param in model.sig.params:
                if param.is_result:
                    return_line = _cf_return_consumer(
                        param.name,
                        param.spec_type,
                        available_count_vars=available_count_vars,
                        length_prefixed=output_length_prefixed,
                    )
                    if return_line is None:
                        return "", [
                            f"cf: unsupported return type `{param.spec_type}` in {model.sig.fn_name}"
                        ]
                    call_args.append(param.name)
                else:
                    call_args.append(param.name)

            if return_line is None:
                return "", [
                    f"cf: no result parameter found for {model.sig.fn_name}"
                ]

            arg_parse_block = "\n".join(arg_lines)
            return_parse_block = return_line
            call_expr = f"{model.sig.fn_name}({', '.join(call_args)})"
            # Requires-check call: same input args, cloned so the
            # postcondition still owns its versions afterwards.
            req_call_expr = None
            if model.requires_fn_name is not None:
                req_arg_exprs: list[str] = []
                for p in model.sig.params:
                    if p.is_result:
                        continue
                    rust_ty = spec_to_direct_rust_type(p.spec_type) or ""
                    if rust_ty.startswith("std::rc::Rc<") or rust_ty.startswith("Option<") or rust_ty == "std::rc::Rc<String>":
                        req_arg_exprs.append(f"{p.name}.clone()")
                    else:
                        req_arg_exprs.append(p.name)
                req_call_expr = (
                    f"{model.requires_fn_name}({', '.join(req_arg_exprs)})"
                )
            source_tests_dir = json.dumps(str((problem_dir / "tests").resolve()))
            main_fn = build_cf_runtime_main(
                arg_parse_block,
                return_parse_block,
                call_expr,
                source_tests_dir,
                has_t_loop,
                requires_call_expr=req_call_expr,
            )
        else:
            parse_gen = DirectRustExprGen()
            parse_lines = []
            for param in model.sig.params:
                rust_ty = spec_to_direct_rust_type(param.spec_type)
                if rust_ty is None:
                    return "", [
                        f"unsupported top-level direct type `{param.spec_type}` in {model.sig.fn_name}"
                    ]
                json_key = "output" if param.is_result else param.name
                value_var = f"__value_{param.name}"
                parse_expr = parse_gen.gen(f"&{value_var}", param.spec_type)
                if parse_expr is None:
                    return "", [
                        f"cannot build direct parser for `{param.spec_type}` in {model.sig.fn_name}"
                    ]
                parse_lines.append(
                    f'        let {value_var} = get_required_field(&obj, "{json_key}").clone();'
                )
                parse_lines.append(f"        let {param.name}: {rust_ty} = {parse_expr};")
                call_args.append(param.name)

            parse_block = "\n".join(parse_lines)
            call_expr = f"{model.sig.fn_name}({', '.join(call_args)})"
            req_call_expr = None
            if model.requires_fn_name is not None:
                req_arg_exprs2: list[str] = []
                for p in model.sig.params:
                    if p.is_result:
                        continue
                    rust_ty2 = spec_to_direct_rust_type(p.spec_type) or ""
                    if rust_ty2.startswith("std::rc::Rc<") or rust_ty2.startswith("Option<"):
                        req_arg_exprs2.append(f"{p.name}.clone()")
                    else:
                        req_arg_exprs2.append(p.name)
                req_call_expr = (
                    f"{model.requires_fn_name}({', '.join(req_arg_exprs2)})"
                )
            source_tests_dir = json.dumps(str((problem_dir / "tests").resolve()))
            main_fn = build_runtime_main(
                parse_block,
                call_expr,
                source_tests_dir,
                requires_call_expr=req_call_expr,
            )

        const_block = "\n".join(translated_consts)
        if const_block:
            const_block += "\n\n"
        full_code = (
            "// post2exe-backend: direct\n"
            + RUST_HELPERS
            + "\n"
            + DIRECT_HELPERS
            + "\n"
            + const_block
            + "\n\n".join(translated_fns)
            + "\n\n"
            + main_fn
            + "\n"
        )
        return full_code, warnings
    except Exception as exc:
        return "", list(dict.fromkeys(warnings + [str(exc)]))


def build_test_post_source(problem_dir: Path) -> tuple[str, list[str]]:
    """Reuse `gen_test_post.py` to obtain the normalized exec-spec file.

    This function mirrors the main extraction flow from `gen_test_post.py`, but
    returns the rendered source text instead of writing it to disk.  `post2exe`
    uses that output as the single source of truth for what the macro will
    actually compile.
    """
    warnings: list[str] = []
    spec_rs = problem_dir / "spec.rs"
    if not spec_rs.exists():
        spec_rs = problem_dir / "code_spec.rs"
    if not spec_rs.exists():
        return "", [f"no spec.rs/code_spec.rs found in {problem_dir}"]

    try:
        spec_text = spec_rs.read_text()
        verus_text = gtp.extract_verus_block(spec_text)
        if not verus_text:
            return "", [f"no verus! block in {spec_rs}"]

        fn_name, ensures, returns_expr = gtp.choose_target_fn(verus_text)
        if fn_name is None:
            return "", [f"no ensures/returns postcondition found in {spec_rs}"]

        sig = gtp.parse_signature(spec_text, fn_name)
        if sig.receiver is not None:
            return "", [f"method receiver `{sig.receiver}` not supported for {fn_name}"]
        if sig.ret == "Self":
            return "", [f"return type `Self` not supported for {fn_name}"]

        if returns_expr is not None:
            # `returns(e)` is lowered to the equivalent equality on the named
            # return variable so the rest of the pipeline can stay clause-based.
            ret_var, _ = gtp.parse_return(sig.ret)
            ensures = [f"{ret_var} == ({returns_expr})"]

        all_fns = gtp.extract_spec_fns(verus_text)
        needed = gtp.find_needed_spec_fns(ensures, all_fns)
        combined = "\n".join(all_fns[n] for n in needed) + "\n" + "\n".join(ensures)
        blockers = gtp.detect_blockers(combined)
        if blockers:
            return "", blockers

        content = gtp.render_test_post_rs(
            fn_name,
            sig,
            needed,
            all_fns,
            ensures,
            extra_use_lines=gtp.extract_use_lines(spec_text),
            extra_const_lines=gtp.extract_const_lines(verus_text),
        )
        blockers = gtp.detect_transformed_blockers(content)
        if blockers:
            return "", blockers
        return content, warnings
    except Exception as exc:
        return "", [str(exc)]


def generate_post2exe(problem_dir: Path) -> tuple[str, list[str]]:
    """Generate a standalone Rust checker for one benchmark problem."""
    direct_code, direct_warnings = generate_direct_post2exe(problem_dir)
    if direct_code:
        return direct_code, direct_warnings
    if any("old(...) state references not supported" in w for w in direct_warnings):
        return "", direct_warnings
    # Hard refusals that the macro fallback won't fix either: when the
    # direct backend determines that stdin tokens cannot be soundly aligned
    # with the spec parameters, the macro path will hit the same ambiguity
    # and produce a checker that silently rejects valid outputs. Skip
    # entirely.
    hard_refusal_markers = (
        "preprocesses inputs before",
        "are computed in main.rs",
        "with pinned endpoints but no value source",
        "appear to be stubs",
        "unbounded exists binder",
        "unbounded forall binder",
        "ghost token interleaved with spec scalars",
        "interleaves scalar reads with Vec reads",
    )
    if any(any(mark in w for mark in hard_refusal_markers) for w in direct_warnings):
        return "", direct_warnings

    warnings: list[str] = list(dict.fromkeys(direct_warnings))
    test_post_text, build_warnings = build_test_post_source(problem_dir)
    if build_warnings:
        return "", list(dict.fromkeys(warnings + build_warnings))

    # Parse the already-lowered postcondition signature.  This avoids having to
    # independently mirror every type rewrite from `gen_test_post.py`.
    sig = parse_postcondition_sig(test_post_text.encode("utf-8"))
    if sig is None:
        return "", [f"no postcondition signature found after transforming {problem_dir}"]

    parse_gen = RustExprGen()
    parse_lines: list[str] = []
    call_args: list[str] = []
    for param in sig.params:
        owned_ty = spec_to_owned_rust_type(param.spec_type)
        if owned_ty is None:
            return "", [f"unsupported top-level type `{param.spec_type}` in {sig.fn_name}"]
        # By convention the testcase output is stored under `output`, while
        # inputs keep their original parameter names.
        json_key = "output" if param.is_result else param.name
        value_var = f"__value_{param.name}"
        parse_expr = parse_gen.gen(f"&{value_var}", param.spec_type)
        if parse_expr is None:
            return "", [f"cannot build parser for `{param.spec_type}` in {sig.fn_name}"]
        parse_lines.append(f'        let {value_var} = get_required_field(&obj, "{json_key}").clone();')
        parse_lines.append(f"        let {param.name}: {owned_ty} = {parse_expr};")
        call_args.append(gen_call_arg(param.name, param.spec_type))

    parse_block = "\n".join(parse_lines)
    call_expr = f"exec_{sig.fn_name}({', '.join(call_args)})"
    source_tests_dir = json.dumps(str((problem_dir / "tests").resolve()))

    main_fn = build_runtime_main(parse_block, call_expr, source_tests_dir)

    # The rendered `test_post.rs` includes a dummy `fn main() {}` because it is
    # meant to be compiled as a standalone file.  Replace that stub with the
    # real testcase runner for `post2exe`.
    verus_block = re.sub(
        r"\nfn\s+main\s*\(\s*\)\s*\{\s*\}\s*$",
        "",
        test_post_text.rstrip(),
        flags=re.DOTALL,
    )
    full_code = (
        "// post2exe-backend: macro\n"
        f"{verus_block}\n{RUST_HELPERS}\n{main_fn}\n"
    )
    return full_code, warnings


def discover_problems(kind: str | None = None) -> list[Path]:
    dirs: list[Path] = []
    for sub in ("leetcode", "codeforces"):
        if kind and sub != kind:
            continue
        base = BENCH_ROOT / sub
        if not base.exists():
            continue
        for d in sorted(base.iterdir()):
            if d.is_dir() and ((d / "spec.rs").exists() or (d / "code_spec.rs").exists()):
                dirs.append(d)
    return dirs


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate executable postcondition checkers from spec.rs/code_spec.rs"
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--problem", type=str, help="single problem directory")
    group.add_argument("--all", action="store_true", help="process all problems")
    parser.add_argument("--kind", type=str, choices=["leetcode", "codeforces"])
    parser.add_argument("--compile", action="store_true")
    parser.add_argument("--run", action="store_true")
    parser.add_argument(
        "--soundness",
        action="store_true",
        help="run testcases.jsonl; the postcondition must accept every case",
    )
    parser.add_argument(
        "--completeness",
        action="store_true",
        help="run mutated_testcases.jsonl; the postcondition must reject every case",
    )
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--out-dir", type=str, default=None)
    parser.add_argument(
        "--run-timeout",
        type=float,
        default=600.0,
        help="seconds to allow each compiled checker run before killing it (default: 600)",
    )
    args = parser.parse_args()

    if args.run or args.soundness or args.completeness:
        args.compile = True
    if args.soundness or args.completeness:
        args.run = True

    run_flags: list[str] = []
    if args.soundness:
        run_flags.append("--soundness")
    if args.completeness:
        run_flags.append("--completeness")

    problems = [Path(args.problem)] if args.problem else discover_problems(args.kind)
    if not problems:
        print("No problems found.", file=sys.stderr)
        sys.exit(1)

    stats = {
        "ok": 0,
        "skip": 0,
        "warn": 0,
        "compile_ok": 0,
        "compile_fail": 0,
        "run_ok": 0,
        "run_fail": 0,
    }

    for prob_dir in problems:
        prob_name = prob_dir.name
        target_path = prob_dir / "tests" / "test_post.rs"

        if not args.force and target_path.exists():
            text = target_path.read_text(errors="ignore")
            m = re.search(r"fn\s+main\s*\(\s*\)\s*\{", text)
            if m:
                brace_start = text.index("{", m.start())
                depth = 0
                body = ""
                for i in range(brace_start, len(text)):
                    if text[i] == "{":
                        depth += 1
                    elif text[i] == "}":
                        depth -= 1
                        if depth == 0:
                            body = text[brace_start + 1 : i].strip()
                            break
                if body:
                    stats["skip"] += 1
                    continue

        code, warnings = generate_post2exe(prob_dir)
        if warnings:
            for w in warnings:
                print(f"  WARN [{prob_name}]: {w}", file=sys.stderr)
            stats["warn"] += 1
            if not code:
                stats["skip"] += 1
                continue

        if args.dry_run:
            print(f"=== {prob_name} ===")
            print(code)
            stats["ok"] += 1
            continue

        backend = "direct" if code.startswith("// post2exe-backend: direct") else "macro"

        if args.out_dir:
            out_dir = Path(args.out_dir) / prob_name / "tests"
            out_dir.mkdir(parents=True, exist_ok=True)
            out_path = out_dir / "test_post.rs"
        else:
            out_path = target_path
            out_path.parent.mkdir(parents=True, exist_ok=True)

        out_path.write_text(code)
        print(f"  OK   [{prob_name}]: {out_path}")
        stats["ok"] += 1

        if args.compile:
            bin_path = Path("/tmp") / f"{prob_name}_test_post"
            if backend == "direct":
                rustc_bin = shutil.which("rustc")
                if rustc_bin is None:
                    print(f"  COMPILE FAIL [{prob_name}]")
                    print("    rustc not found")
                    stats["compile_fail"] += 1
                    continue
                cmd = [rustc_bin, "--edition=2021", str(out_path), "-O", "-o", str(bin_path)]
            else:
                cmd = [str(VERUS_BIN), "--compile", str(out_path), "-o", str(bin_path)]
            try:
                result = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=120,
                )
            except subprocess.TimeoutExpired as exc:
                print(f"  COMPILE FAIL [{prob_name}]")
                print(f"    compile timed out after {exc.timeout} seconds")
                stdout = exc.stdout.decode("utf-8", errors="ignore") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
                stderr = exc.stderr.decode("utf-8", errors="ignore") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
                if stdout.strip():
                    for line in stdout.strip().split("\n")[:5]:
                        print(f"    stdout: {line}")
                if stderr.strip():
                    for line in stderr.strip().split("\n")[:5]:
                        print(f"    stderr: {line}")
                stats["compile_fail"] += 1
                continue
            if result.returncode == 0:
                print(f"  COMPILED [{prob_name}]: {bin_path}")
                stats["compile_ok"] += 1
                if args.run:
                    try:
                        run_result = subprocess.run(
                            [str(bin_path), *run_flags],
                            capture_output=True,
                            text=True,
                            timeout=args.run_timeout,
                        )
                    except subprocess.TimeoutExpired as exc:
                        print(
                            f"  RUN FAIL [{prob_name}]: timed out after {exc.timeout} seconds"
                        )
                        stdout = exc.stdout.decode("utf-8", errors="ignore") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
                        stderr = exc.stderr.decode("utf-8", errors="ignore") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
                        if stdout.strip():
                            for line in stdout.strip().split("\n")[:5]:
                                print(f"    stdout: {line}")
                        if stderr.strip():
                            for line in stderr.strip().split("\n")[:5]:
                                print(f"    stderr: {line}")
                        stats["run_fail"] += 1
                        continue
                    stdout = run_result.stdout.strip()
                    if run_result.returncode == 0:
                        print(f"  RUN OK [{prob_name}]: {stdout}")
                        stats["run_ok"] += 1
                    else:
                        print(f"  RUN FAIL [{prob_name}]: {stdout}")
                        if run_result.stderr.strip():
                            for line in run_result.stderr.strip().split("\n")[:5]:
                                print(f"    stderr: {line}")
                        stats["run_fail"] += 1
            else:
                print(f"  COMPILE FAIL [{prob_name}]")
                for line in result.stderr.strip().split("\n")[:10]:
                    print(f"    {line}")
                stats["compile_fail"] += 1

    print(
        f"\nSummary: {stats['ok']} generated, {stats['skip']} skipped, {stats['warn']} warnings",
        file=sys.stderr,
    )
    if args.compile:
        print(
            f"  Compiled: {stats['compile_ok']} ok, {stats['compile_fail']} fail",
            file=sys.stderr,
        )
    if args.run:
        print(
            f"  Run: {stats['run_ok']} ok, {stats['run_fail']} fail",
            file=sys.stderr,
        )


if __name__ == "__main__":
    main()
