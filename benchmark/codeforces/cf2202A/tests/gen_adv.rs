use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_x: i64, seed_y: i64) -> (result: (i64, i64))
    requires
        1 <= seed_x <= 1_000_000_000,
        -100_000_000 <= seed_y <= 100_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000,
        -100_000_000 <= result.1 <= 100_000_000,
{
    (seed_x, seed_y)
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

fn build_input_multi(cases: &[(i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(x, y) in cases {
        s.push_str(&format!("{} {}\n", x, y));
    }
    s
}

fn build_output_multi(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn solve(x: i64, y: i64) -> bool {
    Solution::parkour_reachable(x, y)
}

fn random_seed(rng: &mut Rng, mode: usize) -> (i64, i64) {
    match mode {
        0 => {
            // Construct exactly reachable
            let a = rng.gen_range_i64(0, 1000);
            let b = rng.gen_range_i64(0, 1000);
            let c = rng.gen_range_i64(0, 1000);
            let x_raw = 2*a + 3*b + 4*c;
            let x = x_raw.max(1).min(1_000_000_000);
            let y_raw = a - c;
            let y = y_raw.max(-100_000_000).min(100_000_000);
            (x, y)
        }
        1 => {
            (rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(-100_000_000, 100_000_000))
        }
        2 => {
            let x = rng.gen_range_i64(1, 1_000_000_000);
            let yb = (x/2).min(100_000_000);
            (x, rng.gen_range_i64(-yb, yb))
        }
        3 => {
            let a = rng.gen_range_i64(0, 100_000_000);
            let b = rng.gen_range_i64(0, 100_000_000);
            let c = rng.gen_range_i64(0, 100_000_000);
            let x_raw = (2*a + 3*b + 4*c).min(1_000_000_000);
            let y_raw = (a - c).max(-100_000_000).min(100_000_000);
            (x_raw.max(1), y_raw)
        }
        4 => (rng.gen_range_i64(1, 50), rng.gen_range_i64(-25, 25)),
        _ => (rng.gen_range_i64(900_000_000, 1_000_000_000), rng.gen_range_i64(-100_000_000, 100_000_000)),
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x2202A);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 50 { rng.gen_range_usize(1, 5) }
                       else if count < 150 { rng.gen_range_usize(5, 50) }
                       else { rng.gen_range_usize(50, 200) };
        let mut cases: Vec<(i64, i64)> = Vec::with_capacity(t);
        for _ in 0..t {
            let mode = rng.gen_range_usize(0, 5);
            let (sx, sy) = random_seed(&mut rng, mode);
            // Validate preconditions
            if sx < 1 || sx > 1_000_000_000 { continue; }
            if sy < -100_000_000 || sy > 100_000_000 { continue; }
            let (x, y) = generate_test_case(sx, sy);
            cases.push((x, y));
        }
        if cases.is_empty() { continue; }
        let answers: Vec<bool> = cases.iter().map(|&(x, y)| solve(x, y)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
