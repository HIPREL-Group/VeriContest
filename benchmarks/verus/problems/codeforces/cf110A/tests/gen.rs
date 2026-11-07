use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u64, mutation_kind: u8) -> (result: u64)
    requires
        1 <= seed <= 1_000_000_000_000_000_000u64,
    ensures
        1 <= result <= 1_000_000_000_000_000_000u64,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 {
        if seed < 1_000_000_000_000_000_000u64 { seed + 1 } else { seed }
    } else if mutation_kind == 2 {
        if seed > 1 { seed - 1 } else { seed }
    } else if mutation_kind == 3 {
        // Replace some digits with 4 or 7
        if seed > 100 { 47 } else { seed }
    } else if mutation_kind == 4 {
        4
    } else if mutation_kind == 5 {
        7
    } else if mutation_kind == 6 {
        47
    } else if mutation_kind == 7 {
        4747
    } else if mutation_kind == 8 {
        4477
    } else if mutation_kind == 9 {
        7777
    } else if mutation_kind == 10 {
        44
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
    let mut seen: HashSet<u64> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: u64, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 1 || n > 1_000_000_000_000_000_000u64 { return; }
        if !seen.insert(n) { return; }
        let result = Solution::nearly_lucky(n);
        let inp = format!("{}\n", n);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Hand-picked
    for &n in &[4u64, 7, 44, 47, 74, 77, 444, 447, 474, 477, 4747, 7444, 7474, 4477, 4444, 7777,
                40047, 7747774, 1_000_000_000_000_000_000u64, 1, 5, 8, 17, 467] {
        emit(n, &mut seen, &mut out, &mut count);
    }

    // Variations
    for s in 1u64..=200u64 {
        for mk in 0u8..11u8 {
            let n = generate_test_case(s, mk);
            emit(n, &mut seen, &mut out, &mut count);
            if count >= target { break; }
        }
        if count >= target { break; }
    }

    let mut s: u64 = 1;
    while count < target {
        emit(s, &mut seen, &mut out, &mut count);
        s = s.saturating_add(s).min(1_000_000_000_000_000_000u64);
        if s >= 1_000_000_000_000_000_000u64 { s = 1; }
        let n2 = generate_test_case(s, 3);
        emit(n2, &mut seen, &mut out, &mut count);
        s += 1;
    }
}
