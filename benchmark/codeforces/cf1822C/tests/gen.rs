use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i64, mutation_kind: u8) -> (result: i64)
    requires
        4 <= seed <= 1_000_000_000i64,
    ensures
        4 <= result <= 1_000_000_000,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 4 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed >= 8 && seed <= 500_000_000 {
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed >= 8 {
            seed / 2                                      // halve (min result is 4)
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        4                                                 // min boundary
    } else if mutation_kind == 6 {
        1_000_000_000                                     // max boundary
    } else if mutation_kind == 7 {
        500_000_000                                       // midpoint
    } else {
        seed                                              // fallback
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
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
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

type TC = i64;

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for n in cases {
        s.push_str(&format!("{}\n", n));
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for n in cases {
        let ans = Solution::bun_chocolate_total(*n);
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1822);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        4, 5, 6, 7, 100, 1000, 1_000_000, 1_000_000_000,
    ];

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 50) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let n = match rng.gen_range_usize(0, 4) {
                0 => rng.gen_range_i64(4, 10),
                1 => rng.gen_range_i64(4, 1000),
                2 => rng.gen_range_i64(4, 1_000_000),
                3 => rng.gen_range_i64(4, 1_000_000_000),
                _ => rng.gen_range_i64(4, 100_000),
            };
            cases.push(n);
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

