use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i64, mutation_kind: u8) -> (result: i64)
    requires
        1 <= seed <= 1000000000000000,
    ensures
        1 <= result <= 1000000000000000,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 1000000000000000 {
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1
    } else if mutation_kind == 3 {
        if seed <= 500000000000000 { seed * 2 } else { seed }
    } else if mutation_kind == 4 {
        seed / 2 + 1
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        1000000000000000
    } else if mutation_kind == 7 {
        500000000000000
    } else {
        seed
    }
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
}

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
    let mut rng = Rng::new(486);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<i64> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i64, seen: &mut HashSet<i64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if n < 1 || n > 1000000000000000 { return; }
        if !seen.insert(n) { return; }
        let result = Solution::calculating_function(n);
        let inp = format!("{}\n", n);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    let edge_cases = [1i64, 2, 3, 4, 5, 6, 7, 8, 9, 10, 100, 999999999999999, 1000000000000000];
    for &n in &edge_cases {
        emit(n, &mut seen, &mut out, &mut count);
    }
    for n in 1i64..=80 {
        emit(n, &mut seen, &mut out, &mut count);
    }
    while count < target_count {
        let seed = rng.gen_range_i64(1, 1000000000000000);
        let kind = (rng.next_u64() % 9) as u8;
        let v = generate_test_case(seed, kind);
        emit(v, &mut seen, &mut out, &mut count);
    }
}
