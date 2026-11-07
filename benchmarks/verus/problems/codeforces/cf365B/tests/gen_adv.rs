use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i64>,
) -> (nums: Vec<i64>)
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut nums: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(values[i]);
        i += 1;
    }
    nums
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

fn build_fib_prefix(n: usize, a: i64, b: i64) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::with_capacity(n);
    if n == 0 { return v; }
    v.push(a.min(1_000_000_000).max(0));
    if n == 1 { return v; }
    v.push(b.min(1_000_000_000).max(0));
    let mut i = 2;
    while i < n {
        let s = v[i-1] + v[i-2];
        if s > 1_000_000_000 {
            while v.len() < n { v.push(0); }
            return v;
        }
        v.push(s);
        i += 1;
    }
    v
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i64> {
    match mode {
        0 => vec![rng.gen_range_i64(0, 1_000_000_000)],
        1 => { let n = rng.gen_range_usize(1, 100); vec![0i64; n] }
        2 => { let n = rng.gen_range_usize(1, 100); vec![1i64; n] }
        3 => { let n = rng.gen_range_usize(2, 45); build_fib_prefix(n, 1, 2) }
        4 => { let n = rng.gen_range_usize(2, 45); build_fib_prefix(n, 0, 1) }
        5 => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| rng.gen_range_i64(0, 10)).collect()
        }
        6 => {
            let n = rng.gen_range_usize(5, 40);
            let mut v = build_fib_prefix(n, 1, 1);
            let idx = n / 2;
            if idx < v.len() {
                v[idx] = (v[idx] + 1).min(1_000_000_000);
            }
            v
        }
        7 => {
            let n1 = rng.gen_range_usize(2, 20);
            let n2 = rng.gen_range_usize(2, 20);
            let mut v = build_fib_prefix(n1, 1, 2);
            let v2 = build_fib_prefix(n2, 3, 5);
            for x in v2 { v.push(x); }
            v
        }
        8 => { let n = 100_000; vec![rng.gen_range_i64(0, 1_000_000_000); n] }
        9 => {
            let n = 100_000;
            (0..n).map(|_| rng.gen_range_i64(0, 1_000_000_000)).collect()
        }
        10 => vec![rng.gen_range_i64(0, 1_000_000_000), rng.gen_range_i64(0, 1_000_000_000)],
        11 => build_fib_prefix(45, 1, 1),
        12 => {
            let mut v = build_fib_prefix(20, 1, 2); v.push(0); v.push(0); v
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| rng.gen_range_i64(0, 1_000_000_000)).collect()
        }
    }
}

fn sanitize(v: Vec<i64>) -> Vec<i64> {
    let mut out = v;
    if out.is_empty() { out.push(0); }
    if out.len() > 100_000 { out.truncate(100_000); }
    for x in out.iter_mut() {
        if *x < 0 { *x = 0; }
        if *x > 1_000_000_000 { *x = 1_000_000_000; }
    }
    out
}

fn build_input(nums: &[i64]) -> String {
    let mut s = format!("{}\n", nums.len());
    let parts: Vec<String> = nums.iter().map(|x| x.to_string()).collect();
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
    let modes = 13usize;
    let mut t = 0usize;
    while count < target {
        let mode = t % modes;
        t += 1;
        let v = sanitize(gen_mode(&mut rng, mode));
        let key = format!("{} {:?}", v.len(), &v[..v.len().min(20)]);
        if !seen.insert(key) { continue; }
        let inp = build_input(&v);
        let ans = Solution::longest_fibonacci_segment(v.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
        if t > 100000 { break; }
    }
}

