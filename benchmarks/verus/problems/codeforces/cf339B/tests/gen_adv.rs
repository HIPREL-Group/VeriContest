use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i64, targets_in: Vec<i64>) -> (result: (i64, Vec<i64>))
    requires
        1 <= n <= 100_000,
        targets_in.len() <= 100_000,
        forall|i: int| 0 <= i < targets_in.len() ==> 1 <= #[trigger] targets_in[i] <= n,
    ensures
        1 <= result.0 <= 100_000,
        result.1.len() <= 100_000,
        result.0 == n,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.0,
{
    (n, targets_in)
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

fn build_targets(rng: &mut Rng, n: i64, m: usize, mode: usize) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::with_capacity(m);
    match mode {
        0 => for _ in 0..m { v.push(rng.gen_range_i64(1, n)); },
        1 => for _ in 0..m { v.push(1); },
        2 => for _ in 0..m { v.push(n); },
        3 => {
            let mut k: i64 = 1;
            for _ in 0..m { v.push(k); k += 1; if k > n { k = 1; } }
        }
        4 => {
            let mut k: i64 = n;
            for _ in 0..m { v.push(k); k -= 1; if k < 1 { k = n; } }
        }
        5 => for i in 0..m { v.push(if i % 2 == 0 { 1 } else { n }); },
        6 => for _ in 0..m { let hi = if n < 3 { n } else { 3 }; v.push(rng.gen_range_i64(1, hi)); },
        7 => for _ in 0..m { let lo = if n > 3 { n - 2 } else { 1 }; v.push(rng.gen_range_i64(lo, n)); },
        8 => { let c = rng.gen_range_i64(1, n); for _ in 0..m { v.push(c); } }
        9 => {
            let mut k = n;
            for _ in 0..m { v.push(k); if k > 1 { k -= 1; } else { k = n; } }
        }
        _ => for _ in 0..m { v.push(rng.gen_range_i64(1, n)); },
    }
    v
}

fn build_input(n: i64, targets: &[i64]) -> String {
    let mut s = format!("{} {}\n", n, targets.len());
    let parts: Vec<String> = targets.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let modes = 10usize;
    let mut t = 0usize;
    while count < target {
        let mode = t % modes;
        t += 1;
        let n: i64 = match mode {
            0 => rng.gen_range_i64(2, 100),
            1 => 2,
            2 => 100_000,
            3 => rng.gen_range_i64(2, 1000),
            4 => rng.gen_range_i64(2, 1000),
            5 => 100_000,
            6 => rng.gen_range_i64(2, 50),
            7 => rng.gen_range_i64(5, 100),
            8 => rng.gen_range_i64(2, 10_000),
            9 => 100_000,
            _ => rng.gen_range_i64(2, 100_000),
        };
        let m: usize = match mode {
            0 => rng.gen_range_usize(1, 100),
            1 => rng.gen_range_usize(1, 100),
            2 => 100_000,
            3 => rng.gen_range_usize(1, 1000),
            4 => rng.gen_range_usize(1, 1000),
            5 => 100_000,
            6 => 1,
            7 => rng.gen_range_usize(1, 500),
            8 => rng.gen_range_usize(1, 10_000),
            9 => 100_000,
            _ => rng.gen_range_usize(1, 100_000),
        };
        let targets = build_targets(&mut rng, n, m, mode);
        if targets.is_empty() { continue; }
        let key = format!("{} {:?}", n, targets);
        if !seen.insert(key) { continue; }
        let inp = build_input(n, &targets);
        let ans = Solution::total_steps(n, targets.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
        if t > 100000 { break; }
    }
}

