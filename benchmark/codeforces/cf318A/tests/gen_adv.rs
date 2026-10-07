use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: u64, k: u64) -> (result: (u64, u64))
    requires
        1 <= k <= n,
        n <= 1_000_000_000_000,
    ensures
        1 <= result.1 <= result.0,
        result.0 <= 1_000_000_000_000,
{
    (n, k)
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
        let r = (hi as u128 - lo as u128 + 1) as u128;
        (lo as u128 + (self.next_u64() as u128) % r) as u64
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

fn pick_case(rng: &mut Rng, mode: usize) -> (u64, u64) {
    let nmax: u64 = 1_000_000_000_000;
    match mode {
        0 => (1, 1),
        1 => (nmax, 1),
        2 => (nmax, nmax),
        3 => {
            let n = rng.gen_range_u64(1, nmax);
            let k = (n + 1) / 2;
            (n, k)
        }
        4 => {
            let n = rng.gen_range_u64(2, nmax);
            let k = (n + 1) / 2 + 1;
            let k = if k > n { n } else { k };
            (n, k)
        }
        5 => {
            let n = rng.gen_range_u64(1, 20);
            let k = rng.gen_range_u64(1, n);
            (n, k)
        }
        6 => {
            let n = rng.gen_range_u64(1, 500_000_000_000) * 2;
            let n = if n > nmax { nmax } else if n < 1 { 1 } else { n };
            let k = rng.gen_range_u64(1, n);
            (n, k)
        }
        7 => {
            let n = rng.gen_range_u64(1, 499_999_999_999) * 2 + 1;
            let n = if n > nmax { nmax } else { n };
            let k = rng.gen_range_u64(1, n);
            (n, k)
        }
        8 => {
            let n = nmax;
            let k = rng.gen_range_u64(1, n);
            (n, k)
        }
        9 => {
            let n = rng.gen_range_u64(2, nmax);
            let mid = (n + 1) / 2;
            let off = rng.gen_range_u64(0, 2);
            let k = if mid + off > n { n } else { mid + off };
            let k = if k < 1 { 1 } else { k };
            (n, k)
        }
        _ => {
            let n = rng.gen_range_u64(1, nmax);
            let k = rng.gen_range_u64(1, n);
            (n, k)
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let modes = 11usize;
    let mut t = 0usize;
    while count < target {
        let mode = t % modes;
        t += 1;
        let (n, k) = pick_case(&mut rng, mode);
        if !(1 <= k && k <= n && n <= 1_000_000_000_000) { continue; }
        let key = format!("{} {}", n, k);
        if !seen.insert(key) { continue; }
        let inp = format!("{} {}\n", n, k);
        let ans = Solution::kth_even_odds(n, k);
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
        if t > 100000 { break; }
    }
}

