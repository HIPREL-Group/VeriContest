use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i64, m: i64, k: i64) -> (result: (i64, i64, i64))
    requires
        2 <= k <= n <= 1_000_000_000,
        0 <= m <= n,
    ensures
        ({
            let (rn, rm, rk) = result;
            &&& 2 <= rk <= rn <= 1_000_000_000
            &&& 0 <= rm <= rn
        }),
{
    (n, m, k)
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

fn pick_case(rng: &mut Rng, mode: usize) -> (i64, i64, i64) {
    match mode {
        0 => {
            let n = rng.gen_range_i64(2, 10);
            let m = rng.gen_range_i64(0, n);
            let k = rng.gen_range_i64(2, n);
            (n, m, k)
        }
        1 => {
            let n = rng.gen_range_i64(2, 1_000_000_000);
            let m = rng.gen_range_i64(0, n);
            (n, m, 2)
        }
        2 => {
            let n = rng.gen_range_i64(2, 1_000_000_000);
            let m = rng.gen_range_i64(0, n);
            (n, m, n)
        }
        3 => {
            let n = rng.gen_range_i64(2, 1_000_000_000);
            let k = rng.gen_range_i64(2, n);
            (n, n, k)
        }
        4 => {
            let n = rng.gen_range_i64(2, 1_000_000_000);
            let k = rng.gen_range_i64(2, n);
            (n, 0, k)
        }
        5 => {
            let k = rng.gen_range_i64(2, 100);
            let wrong = rng.gen_range_i64(0, 1000);
            let m = (wrong + 1) * (k - 1);
            let n = m + wrong;
            if n >= 2 && n <= 1_000_000_000 && k <= n && m <= n && m >= 0 { (n, m, k) } else { (2, 0, 2) }
        }
        6 => {
            let k = rng.gen_range_i64(2, 100);
            let wrong = rng.gen_range_i64(0, 1000);
            let m = (wrong + 1) * (k - 1) + 1;
            let n = m + wrong;
            if n >= 2 && n <= 1_000_000_000 && k <= n && m <= n && m >= 0 { (n, m, k) } else { (2, 2, 2) }
        }
        7 => {
            let n = rng.gen_range_i64(999_000_000, 1_000_000_000);
            let m = rng.gen_range_i64(0, n);
            let k = rng.gen_range_i64(2, n);
            (n, m, k)
        }
        8 => {
            let n = rng.gen_range_i64(999_000_000, 1_000_000_000);
            let k = rng.gen_range_i64(2, 10);
            (n, n, k)
        }
        9 => {
            let m = rng.gen_range_i64(0, 2);
            (2, m, 2)
        }
        _ => {
            let n = rng.gen_range_i64(2, 100_000);
            let m = rng.gen_range_i64(0, n);
            let k = rng.gen_range_i64(2, n);
            (n, m, k)
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
        let (n, m, k) = pick_case(&mut rng, mode);
        if !(2 <= k && k <= n && n <= 1_000_000_000 && 0 <= m && m <= n) { continue; }
        let key = format!("{} {} {}", n, m, k);
        if !seen.insert(key) { continue; }
        let inp = format!("{} {} {}\n", n, m, k);
        let ans = Solution::min_quiz_score(n, m, k);
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
        if t > 100000 { break; }
    }
}

