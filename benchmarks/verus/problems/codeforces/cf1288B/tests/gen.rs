use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: i64, seed_b: i64, mutation_kind: u8) -> (res: (i64, i64))
    requires
        1 <= seed_a <= 1_000_000_000,
        1 <= seed_b <= 1_000_000_000,
    ensures
        1 <= res.0 <= 1_000_000_000,
        1 <= res.1 <= 1_000_000_000,
{
    let a = if mutation_kind == 0 {
        seed_a                                          // identity
    } else if mutation_kind == 1 && seed_a < 1_000_000_000 {
        seed_a + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_a > 1 {
        seed_a - 1                                      // nudge down
    } else if mutation_kind == 3 && seed_a <= 500_000_000 {
        seed_a * 2                                      // double
    } else if mutation_kind == 4 {
        let h = seed_a / 2;
        if h < 1 { 1i64 } else { h }                   // halve
    } else if mutation_kind == 5 {
        1                                               // min boundary
    } else if mutation_kind == 6 {
        1_000_000_000                                   // max boundary
    } else {
        seed_a                                          // fallback
    };

    let b = if mutation_kind == 7 && seed_b < 1_000_000_000 {
        seed_b + 1                                      // nudge up
    } else if mutation_kind == 8 && seed_b > 1 {
        seed_b - 1                                      // nudge down
    } else if mutation_kind == 9 && seed_b <= 500_000_000 {
        seed_b * 2                                      // double
    } else if mutation_kind == 10 {
        let h = seed_b / 2;
        if h < 1 { 1i64 } else { h }                   // halve
    } else if mutation_kind == 11 {
        1                                               // min boundary
    } else if mutation_kind == 12 {
        1_000_000_000                                   // max boundary
    } else if mutation_kind == 13 {
        // set b = a (same value)
        if seed_a >= 1 && seed_a <= 1_000_000_000 { seed_a } else { seed_b }
    } else {
        seed_b                                          // fallback
    };

    (a, b)
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

fn build_input(cases: &[(i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(a,b) in cases { s.push_str(&format!("{} {}\n", a, b)); }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |cases: Vec<(i64,i64)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64; h = h.wrapping_mul(1099511628211);
        for &(a,b) in &cases {
            h ^= a as u64; h = h.wrapping_mul(1099511628211);
            h ^= b as u64; h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let answers: Vec<i64> = cases.iter().map(|&(a,b)| Solution::meme_pair_count(a,b)).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Example
    let example = vec![(1i64,1),(4,2),(191,31415926)];
    emit(example, &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![(1i64, 1)], &mut seen, &mut out, &mut count);
    emit(vec![(1_000_000_000, 1_000_000_000)], &mut seen, &mut out, &mut count);
    emit(vec![(9, 9)], &mut seen, &mut out, &mut count);
    emit(vec![(99, 99)], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let t: usize = if tries < 5 { 1 } else { rng.gen_range_usize(2, 50) };
        let mut cases: Vec<(i64,i64)> = Vec::new();
        for _ in 0..t {
            let max_v = match tries % 4 {
                0 => 10i64,
                1 => 100,
                2 => 1_000_000,
                _ => 1_000_000_000,
            };
            let a = rng.gen_range_i64(1, max_v);
            let b = rng.gen_range_i64(1, max_v);
            cases.push((a,b));
        }
        emit(cases, &mut seen, &mut out, &mut count);
    }
}

