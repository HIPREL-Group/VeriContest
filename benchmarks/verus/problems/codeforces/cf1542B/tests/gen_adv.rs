use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i64, a_val: i64, b_val: i64) -> (res: (i64, i64, i64))
    requires
        1 <= n_val <= 1_000_000_000,
        1 <= a_val <= 1_000_000_000,
        1 <= b_val <= 1_000_000_000,
    ensures
        ({
            let (n, a, b) = res;
            1 <= n <= 1_000_000_000
            && 1 <= a <= 1_000_000_000
            && 1 <= b <= 1_000_000_000
        }),
{
    (n_val, a_val, b_val)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng { state: u64 }
impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        lo + ((self.next_u64() as u128) % span) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
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

fn clamp(v: i64, lo: i64, hi: i64) -> i64 { if v < lo { lo } else if v > hi { hi } else { v } }

fn pick(rng: &mut Rng, mode: usize) -> (i64, i64, i64) {
    let max_v: i64 = 1_000_000_000;
    match mode {
        0 => { let n = rng.gen_range_i64(1, max_v); let b = rng.gen_range_i64(1, max_v); (n, 1, b) }
        1 => { let n = rng.gen_range_i64(1, max_v); let a = rng.gen_range_i64(1, max_v); (n, a, 1) }
        2 => { let a = rng.gen_range_i64(1, max_v); let b = rng.gen_range_i64(1, max_v); (1, a, b) }
        3 => {
            let a = rng.gen_range_i64(2, 50);
            let b = rng.gen_range_i64(1, max_v);
            let k = rng.gen_range_usize(0, 30);
            let mut p: i64 = 1;
            let mut i: usize = 0;
            while i < k && p <= max_v / a { p = p * a; i += 1; }
            if p > max_v { p = 1; }
            let remaining = max_v - p;
            let m_max = if b == 0 { 0 } else { remaining / b };
            let m = if m_max == 0 { 0 } else { rng.gen_range_i64(0, m_max) };
            let n = clamp(p + m * b, 1, max_v);
            (n, a, b)
        }
        4 => { let a = rng.gen_range_i64(500_000_000, max_v); let b = rng.gen_range_i64(500_000_000, max_v); let n = rng.gen_range_i64(1, 1000); (n, a, b) }
        5 => (max_v, max_v, max_v),
        6 => { let n = rng.gen_range_i64(1, 100); let a = rng.gen_range_i64(1, 10); let b = rng.gen_range_i64(1, 10); (n, a, b) }
        7 => { let n = rng.gen_range_i64(1, max_v); let b = rng.gen_range_i64(1, max_v); (n, 2, b) }
        8 => { let a = rng.gen_range_i64(2, max_v); let b = rng.gen_range_i64(1, 100); let n = rng.gen_range_i64(1, max_v); (n, a, b) }
        9 => {
            let b = rng.gen_range_i64(1, 1_000_000);
            let k = rng.gen_range_i64(0, max_v / b - 1);
            let n = clamp(k * b + 1, 1, max_v);
            let a = rng.gen_range_i64(1, max_v);
            (n, a, b)
        }
        _ => { let n = rng.gen_range_i64(1, max_v); let a = rng.gen_range_i64(1, max_v); let b = rng.gen_range_i64(1, max_v); (n, a, b) }
    }
}

fn build_input(cases: &[(i64, i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(n, a, b) in cases {
        s.push_str(&format!("{} {} {}\n", n, a, b));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "Yes\n" } else { "No\n" });
    }
    s
}

fn main() {
    let mut rng = Rng::new(1);
    let total = 200usize;
    let modes = 11usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut idx = 0usize;
    while count < total {
        // Bundle multiple sub-tests per entry
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 50) };
        let mut cases: Vec<(i64, i64, i64)> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            let (n_in, a_in, b_in) = pick(&mut rng, mode);
            let n = clamp(n_in, 1, 1_000_000_000);
            let a = clamp(a_in, 1, 1_000_000_000);
            let b = clamp(b_in, 1, 1_000_000_000);
            cases.push((n, a, b));
        }
        let answers: Vec<bool> = cases.iter().map(|&(n, a, b)| Solution::n_in_generated_set(n, a, b)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }
}

