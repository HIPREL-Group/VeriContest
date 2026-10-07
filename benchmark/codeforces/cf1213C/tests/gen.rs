use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: u64, seed_m: u64, mutation_kind: u8) -> (res: (u64, u64))
    requires
        1 <= seed_n <= 10_000_000_000_000_000,
        1 <= seed_m <= 10_000_000_000_000_000,
    ensures
        1 <= res.0 <= 10_000_000_000_000_000,
        1 <= res.1 <= 10_000_000_000_000_000,
{
    let n = if mutation_kind == 0 {
        seed_n                                              // identity
    } else if mutation_kind == 1 && seed_n < 10_000_000_000_000_000 {
        seed_n + 1                                          // nudge up
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1                                          // nudge down
    } else if mutation_kind == 3 && seed_n <= 5_000_000_000_000_000 {
        seed_n * 2                                          // double
    } else if mutation_kind == 4 {
        let h = seed_n / 2;
        if h >= 1 { h } else { 1u64 }                      // halve (clamp to 1)
    } else if mutation_kind == 5 {
        1u64                                                // min boundary
    } else if mutation_kind == 6 {
        10_000_000_000_000_000u64                           // max boundary
    } else {
        seed_n                                              // fallback
    };

    let m = if mutation_kind == 7 && seed_m < 10_000_000_000_000_000 {
        seed_m + 1                                          // nudge up m
    } else if mutation_kind == 8 && seed_m > 1 {
        seed_m - 1                                          // nudge down m
    } else if mutation_kind == 9 {
        seed_n                                              // m = n
    } else if mutation_kind == 10 && seed_m <= 5_000_000_000_000_000 {
        seed_m * 2                                          // double m
    } else if mutation_kind == 11 {
        1u64                                                // min m
    } else if mutation_kind == 12 {
        10_000_000_000_000_000u64                           // max m
    } else {
        seed_m                                              // fallback
    };

    (n, m)
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
        let r = hi - lo + 1;
        lo + (self.next_u64() % r)
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

fn build_input(cases: &[(u64, u64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(n, m) in cases {
        s.push_str(&format!("{} {}\n", n, m));
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
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |cases: Vec<(u64,u64)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64; h = h.wrapping_mul(1099511628211);
        for &(n, m) in &cases {
            h ^= n; h = h.wrapping_mul(1099511628211);
            h ^= m; h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let answers: Vec<u64> = cases.iter().map(|&(n, m)| Solution::book_reading_digit_sum(n, m)).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Example
    let example = vec![(1,1),(10,1),(100,3),(1024,14),(998_244_353,1337),(123,144),(1_234_312_817_382_646,13)];
    emit(example, &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![(1u64,1u64)], &mut seen, &mut out, &mut count);
    emit(vec![(10_000_000_000_000_000u64, 10_000_000_000_000_000u64)], &mut seen, &mut out, &mut count);
    emit(vec![(1u64, 10_000_000_000_000_000u64)], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let q: usize = if tries < 5 { 1 } else { rng.gen_range_usize(2, 50) };
        let mut cases: Vec<(u64,u64)> = Vec::new();
        for _ in 0..q {
            let max_v = match tries % 5 {
                0 => 10u64,
                1 => 100,
                2 => 100_000,
                3 => 1_000_000_000,
                _ => 10_000_000_000_000_000,
            };
            let n = rng.gen_range_u64(1, max_v);
            let m = rng.gen_range_u64(1, max_v);
            cases.push((n, m));
        }
        emit(cases, &mut seen, &mut out, &mut count);
    }
}

