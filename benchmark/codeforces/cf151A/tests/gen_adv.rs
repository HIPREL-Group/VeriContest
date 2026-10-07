use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: u64, k: u64, l: u64, c: u64, d: u64, p: u64, nl: u64, np: u64) -> (result: (u64, u64, u64, u64, u64, u64, u64, u64))
    requires
        1 <= n <= 1000,
        1 <= k <= 1000,
        1 <= l <= 1000,
        1 <= c <= 1000,
        1 <= d <= 1000,
        1 <= p <= 1000,
        1 <= nl <= 1000,
        1 <= np <= 1000,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= 1000,
        1 <= result.2 <= 1000,
        1 <= result.3 <= 1000,
        1 <= result.4 <= 1000,
        1 <= result.5 <= 1000,
        1 <= result.6 <= 1000,
        1 <= result.7 <= 1000,
{
    (n, k, l, c, d, p, nl, np)
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
        lo + self.next_u64() % (hi - lo + 1)
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

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x151AA);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = rng.gen_range_u64(1, 1000);
        let k = rng.gen_range_u64(1, 1000);
        let l = rng.gen_range_u64(1, 1000);
        let c = rng.gen_range_u64(1, 1000);
        let d = rng.gen_range_u64(1, 1000);
        let p = rng.gen_range_u64(1, 1000);
        let nl = rng.gen_range_u64(1, 1000);
        let np = rng.gen_range_u64(1, 1000);
        let inp = match tries % 3 {
            0 => format!("{} {} {} {} {} {} {} {}\n", n, k, l, c, d, p, nl, np),
            1 => format!("{} {} {} {} {} {} {} {}", n, k, l, c, d, p, nl, np),
            _ => format!(" {} {} {} {} {} {} {} {} \n", n, k, l, c, d, p, nl, np),
        };
        if !seen.insert(inp.clone()) { continue; }
        let res = Solution::max_toasts(n, k, l, c, d, p, nl, np);
        let outp = format!("{}\n", res);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
