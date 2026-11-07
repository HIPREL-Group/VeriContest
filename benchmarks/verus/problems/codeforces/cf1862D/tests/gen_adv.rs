use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: u64) -> (out: u64)
    requires
        1 <= n <= 1_000_000_000_000_000_000u64,
    ensures
        out == n,
{
    n
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
    for n in cases { s.push_str(&format!("{}\n", n)); }
    s
}

fn build_output(answers: &[u64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn pick_adv(rng: &mut Rng) -> u64 {
    match rng.next_u64() % 6 {
        0 => {
            // Triangle number m*(m-1)/2 for some m
            let m = rng.gen_range_u64(2, 1_000_000_000);
            if m % 2 == 0 { (m / 2) * (m - 1) } else { m * ((m - 1) / 2) }
        }
        1 => {
            // Triangle + 1
            let m = rng.gen_range_u64(2, 1_000_000_000);
            let t = if m % 2 == 0 { (m / 2) * (m - 1) } else { m * ((m - 1) / 2) };
            t + 1
        }
        2 => {
            // Triangle - 1
            let m = rng.gen_range_u64(2, 1_000_000_000);
            let t = if m % 2 == 0 { (m / 2) * (m - 1) } else { m * ((m - 1) / 2) };
            if t > 1 { t - 1 } else { 1 }
        }
        3 => 1_000_000_000_000_000_000,
        4 => 1,
        _ => rng.gen_range_u64(1, 1_000_000_000_000_000_000),
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(10, 30) } else { rng.gen_range_usize(20, 100) };
        let mut cases: Vec<u64> = Vec::new();
        for _ in 0..t {
            cases.push(pick_adv(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<u64> = cases.iter().map(|&n| Solution::min_balls_for_types(n)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

