use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i64, b: i64, c: i64) -> (res: (i64, i64, i64))
    requires
        0 <= a <= 20,
        0 <= b <= 20,
        0 <= c <= 20,
    ensures
        0 <= res.0 <= 20,
        0 <= res.1 <= 20,
        0 <= res.2 <= 20,
{
    (a, b, c)
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

type TC = (i64, i64, i64);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b, c) in cases {
        s.push_str(&format!("{} {} {}\n", a, b, c));
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (a, b, c) in cases {
        if Solution::one_is_sum_of_others(*a, *b, *c) {
            s.push_str("YES\n");
        } else {
            s.push_str("NO\n");
        }
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1742);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 200000 {
        tries += 1;
        let t: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(2, 50),
            2 => rng.gen_range_usize(50, 200),
            3 => rng.gen_range_usize(200, 500),
            _ => rng.gen_range_usize(2, 100),
        };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = rng.gen_range_usize(0, 4);
            let (a, b, c) = match mode {
                0 => {
                    // edge: zeros
                    (rng.gen_range_i64(0, 5), rng.gen_range_i64(0, 5), rng.gen_range_i64(0, 5))
                }
                1 => {
                    // edge: max
                    (rng.gen_range_i64(15, 20), rng.gen_range_i64(15, 20), rng.gen_range_i64(15, 20))
                }
                2 => {
                    // force YES (a + b = c)
                    let a = rng.gen_range_i64(0, 10);
                    let b = rng.gen_range_i64(0, 10);
                    let c = a + b;
                    (a, b, c)
                }
                _ => {
                    (rng.gen_range_i64(0, 20), rng.gen_range_i64(0, 20), rng.gen_range_i64(0, 20))
                }
            };
            cases.push((a, b, c));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

