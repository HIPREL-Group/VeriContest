use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u64, mutation_kind: u8) -> (result: u64)
    requires
        1 <= seed <= 1_000_000_000_000_000_000u64,
    ensures
        1 <= result <= 1_000_000_000_000_000_000u64,
{
    if mutation_kind == 0 {
        seed                                                          // identity
    } else if mutation_kind == 1 && seed < 1_000_000_000_000_000_000u64 {
        seed + 1                                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 500_000_000_000_000_000u64 {
            seed * 2                                                  // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        let h = seed / 2;
        if h >= 1 { h } else { 1u64 }                                // halve
    } else if mutation_kind == 5 {
        1u64                                                          // min boundary
    } else if mutation_kind == 6 {
        1_000_000_000_000_000_000u64                                  // max boundary
    } else if mutation_kind == 7 {
        // clamp to triangular number region: tri(m) = m*(m-1)/2, m=2 => 1
        // just return small value
        if seed <= 10 { seed } else { 10u64 }                        // small value
    } else if mutation_kind == 8 {
        // near-max boundary
        if seed > 999_999_999_999_999_000u64 {
            seed
        } else {
            999_999_999_999_999_999u64
        }
    } else if mutation_kind == 9 {
        // square root region: interesting for binary search
        let s = 1_000_000_000u64;
        if s >= 1 { s } else { 1u64 }
    } else {
        seed                                                          // fallback
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
    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        lo + (self.next_u64() % (hi - lo + 1))
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

fn build_input(cases: &[u64]) -> String {
    let mut s = format!("{}\n", cases.len());
    for n in cases {
        s.push_str(&format!("{}\n", n));
    }
    s
}

fn build_output(answers: &[u64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1862);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Example
    let example: Vec<u64> = vec![1, 3, 6, 179, 1_000_000_000_000_000_000];
    {
        let inp = build_input(&example);
        let answers: Vec<u64> = example.iter().map(|&n| Solution::min_balls_for_types(n)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Edge cases - triangle numbers
    let edges: Vec<u64> = vec![1, 2, 3, 4, 5, 6, 10, 15, 21, 28, 36, 45, 55, 100, 1000, 1_000_000_000, u64::MAX / 2, 1_000_000_000_000_000_000];
    for &n in &edges {
        if count >= target { break; }
        let cases = vec![n];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<u64> = cases.iter().map(|&n| Solution::min_balls_for_types(n)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 8) } else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<u64> = Vec::new();
        for _ in 0..t {
            let scale = match rng.next_u64() % 5 {
                0 => 100u64,
                1 => 10_000,
                2 => 1_000_000,
                3 => 1_000_000_000,
                _ => 1_000_000_000_000_000_000,
            };
            cases.push(rng.gen_range_u64(1, scale));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<u64> = cases.iter().map(|&n| Solution::min_balls_for_types(n)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

