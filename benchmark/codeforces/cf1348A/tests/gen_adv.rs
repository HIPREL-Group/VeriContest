use vstd::prelude::*;

verus! {

pub fn generate_test_case(half: i32) -> (n: i32)
    requires
        1 <= half <= 15,
    ensures
        2 <= n <= 30,
        (n as int) % 2 == 0,
{
    let n = 2 * half;
    assert((n as int) % 2 == 0) by (compute);
    n
}

}

use std::io::Write;

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

fn build_input(ns: &[i32]) -> String {
    let mut s = format!("{}\n", ns.len());
    for n in ns {
        s.push_str(&format!("{}\n", n));
    }
    s
}

fn build_output(ans: &[i64]) -> String {
    let mut s = String::new();
    for a in ans {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Examples
    {
        let ns = vec![2i32, 4];
        let answers: Vec<i64> = ns.iter().map(|&n| Solution::phoenix_balance_min_diff(n)).collect();
        let inp = build_input(&ns);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    // boundary: just n=2 and just n=30
    for &n in &[2i32, 30] {
        let ns = vec![n];
        let answers: Vec<i64> = ns.iter().map(|&n| Solution::phoenix_balance_min_diff(n)).collect();
        let inp = build_input(&ns);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    // All evens from 2 to 30 in one large bundle (extreme case)
    {
        let ns: Vec<i32> = (1..=15).map(|i| 2 * i).collect();
        let answers: Vec<i64> = ns.iter().map(|&n| Solution::phoenix_balance_min_diff(n)).collect();
        let inp = build_input(&ns);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 4usize;
    while count < target {
        let t: usize = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => 100,
        };
        let mut ns: Vec<i32> = Vec::new();
        for _ in 0..t {
            let mode = rng.next_u64() % 5;
            let n = match mode {
                0 => 2,
                1 => 30,
                2 => 16,
                3 => (rng.gen_range_i64(1, 15) * 2) as i32,
                _ => (rng.gen_range_i64(1, 15) * 2) as i32,
            };
            ns.push(n);
        }
        let answers: Vec<i64> = ns.iter().map(|&n| Solution::phoenix_balance_min_diff(n)).collect();
        let inp = build_input(&ns);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

