use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_m: u32, seed_n: u32, mutation_kind: u8)
    -> (result: (u32, u32))
    requires
        1 <= seed_m <= 16,
        1 <= seed_n <= 16,
    ensures
        1 <= result.0 <= 16,
        1 <= result.1 <= 16,
{
    let mut m = seed_m;
    let mut n = seed_n;

    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 && m < 16 {
        m = m + 1;                           // nudge m up
    } else if mutation_kind == 2 && m > 1 {
        m = m - 1;                           // nudge m down
    } else if mutation_kind == 3 && n < 16 {
        n = n + 1;                           // nudge n up
    } else if mutation_kind == 4 && n > 1 {
        n = n - 1;                           // nudge n down
    } else if mutation_kind == 5 {
        m = 1;                               // min m
    } else if mutation_kind == 6 {
        m = 16;                              // max m
    } else if mutation_kind == 7 {
        n = 1;                               // min n
    } else if mutation_kind == 8 {
        n = 16;                              // max n
    } else if mutation_kind == 9 {
        if m <= 8 {
            m = m * 2;                       // double m
        }
    } else if mutation_kind == 10 {
        m = m / 2 + 1;                       // halve m (stay >= 1)
    } else if mutation_kind == 11 {
        if n <= 8 {
            n = n * 2;                       // double n
        }
    } else if mutation_kind == 12 {
        n = n / 2 + 1;                       // halve n (stay >= 1)
    } else if mutation_kind == 13 {
        m = seed_n;
        n = seed_m;                          // swap m and n
    } else if mutation_kind == 14 {
        m = seed_n;
        n = seed_n;                          // m == n (square board)
    } else if mutation_kind == 15 {
        m = 1;
        n = 1;                               // minimal board
    } else if mutation_kind == 16 {
        m = 16;
        n = 16;                              // maximal board
    } else {
        // fallback: identity
    }

    (m, n)
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
    let target_count: usize = 100;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |m: u32, n: u32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if m < 1 || n < 1 || m > n || n > 16 { return; }
        let key = format!("{}_{}", m, n);
        if !seen.insert(key) { return; }
        let result = Solution::max_dominoes(m, n);
        let inp = format!("{} {}\n", m, n);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(2, 4, &mut seen, &mut out, &mut count);
    emit(3, 3, &mut seen, &mut out, &mut count);

    for m in 1u32..=16 {
        for n in m..=16 {
            emit(m, n, &mut seen, &mut out, &mut count);
        }
    }
}

