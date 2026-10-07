use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u32, mutation_kind: u8) -> (result: u32)
    requires
        3 <= seed <= 500,
    ensures
        3 <= result <= 500,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 {
        if seed < 500 { seed + 1 } else { seed }
    } else if mutation_kind == 2 {
        if seed > 3 { seed - 1 } else { seed }
    } else if mutation_kind == 3 {
        3
    } else if mutation_kind == 4 {
        500
    } else if mutation_kind == 5 {
        if seed >= 250 { seed } else { seed * 2 }
    } else {
        seed
    }
}

}

use std::io::Write;
use std::collections::HashSet;

fn fmt_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

struct Solution;
include!("../code.rs");

fn main() {
    let target: usize = 100;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<u32> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: u32, seen: &mut HashSet<u32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 3 || n > 500 { return; }
        if !seen.insert(n) { return; }
        let result = Solution::min_triangulation(n);
        let inp = format!("{}\n", n);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    for n in 3..=200u32 {
        emit(n, &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }
    let mut s: u32 = 3;
    while count < target {
        for mk in 0u8..7u8 {
            let n = generate_test_case(s, mk);
            emit(n, &mut seen, &mut out, &mut count);
        }
        s = if s >= 500 { 3 } else { s + 1 };
    }
}
