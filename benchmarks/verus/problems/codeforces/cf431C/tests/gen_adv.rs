use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, k: i32, d: i32) -> (result: (i32, i32, i32))
    requires
        1 <= n <= 100,
        1 <= k <= 100,
        1 <= d <= k,
    ensures
        ({
            let (rn, rk, rd) = result;
            &&& 1 <= rn <= 100
            &&& 1 <= rk <= 100
            &&& 1 <= rd <= rk
        }),
{
    (n, k, d)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i32, k: i32, d: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(1 <= n && n <= 100 && 1 <= k && k <= 100 && 1 <= d && d <= k) { return; }
        let key = format!("{} {} {}", n, k, d);
        if !seen.insert(key) { return; }
        let inp = format!("{} {} {}\n", n, k, d);
        let ans = Solution::count_k_tree_paths(n, k, d);
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // exhaustive small
    for n in 1..=10 {
        for k in 1..=10 {
            for d in 1..=k {
                emit(n, k, d, &mut seen, &mut out, &mut count);
                if count >= target { return; }
            }
        }
    }
    // boundary cases
    for n in [1, 100].iter() {
        for k in [1, 100].iter() {
            for d in [1, *k].iter() {
                emit(*n, *k, *d, &mut seen, &mut out, &mut count);
            }
        }
    }
    // random
    while count < target {
        let n = rng.gen_range_i32(1, 100);
        let k = rng.gen_range_i32(1, 100);
        let d = rng.gen_range_i32(1, k);
        emit(n, k, d, &mut seen, &mut out, &mut count);
    }
}

