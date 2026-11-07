use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: u64, m_val: u64) -> (r: (u64, u64))
    requires
        1 <= n_val <= 10_000_000_000_000_000,
        1 <= m_val <= 10_000_000_000_000_000,
    ensures
        1 <= r.0 <= 10_000_000_000_000_000,
        1 <= r.1 <= 10_000_000_000_000_000,
{
    (n_val, m_val)
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
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    // Edge boundary values
    let bounds = vec![1u64, 2, 5, 9, 10, 11, 99, 100, 1000, 9999, 1_000_000, 1_000_000_000_000, 10_000_000_000_000_000];
    let mut single_cases = Vec::new();
    for &n in &bounds {
        for &m in &bounds {
            single_cases.push((n, m));
        }
    }
    // bundle them in groups of 10
    for chunk in single_cases.chunks(10) {
        emit(chunk.to_vec(), &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let q: usize = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
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

