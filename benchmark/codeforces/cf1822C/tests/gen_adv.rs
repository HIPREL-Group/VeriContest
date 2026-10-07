use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i64) -> (r: i64)
    requires
        4 <= n <= 1_000_000_000,
    ensures
        4 <= r <= 1_000_000_000,
{
    n
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed.wrapping_add(1)) }
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
    let target: usize = 200;
    let mut rng = Rng::new(1822);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(2, 100),
            2 => rng.gen_range_usize(100, 1000),
            3 => rng.gen_range_usize(1000, 10000),
            _ => rng.gen_range_usize(2, 500),
        };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let n = match rng.gen_range_usize(0, 4) {
                0 => rng.gen_range_i64(4, 10),
                1 => 4,
                2 => 1_000_000_000,
                3 => rng.gen_range_i64(4, 1_000_000_000),
                _ => rng.gen_range_i64(4, 1_000_000),
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

