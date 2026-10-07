use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>) -> (result: Vec<i64>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000000000,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 100000 { 100000usize } else { values.len() };
    let limit = 1000000000;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000,
            limit == 1000000000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= limit,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > limit { limit } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(values: &Vec<i64>) -> (a: Vec<i64>)
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= a.len() <= 100_000,
        a.len() == values.len(),
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < a.len() ==> a[i] == values[i],
{
    let n = values.len();
    let mut a: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            n == values.len(),
            0 <= idx <= n,
            a.len() == idx,
            forall|i: int| 0 <= i < idx as int ==> #[trigger] a[i] == values[i],
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
        decreases n - idx,
    {
        a.push(values[idx]);
        idx = idx + 1;
    }
    a
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
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as u128;
        (lo as i128 + (v % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % (hi - lo + 1)
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

fn build_input(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers { s.push_str(if a { "YES\n" } else { "NO\n" }); }
    s
}

fn make_test(rng: &mut Rng, mode: usize) -> Vec<i64> {
    match mode {
        0 => vec![rng.gen_range_i64(1, 1_000_000_000)],
        1 => vec![2],
        2 => {
            let n = rng.gen_range_usize(1, 50);
            vec![1; n]
        }
        3 => {
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| rng.gen_range_i64(1, 100)).collect()
        }
        4 => {
            // Easy YES: all primes >= n+2
            let n = rng.gen_range_usize(1, 30);
            let primes: Vec<i64> = vec![2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173];
            (0..n).map(|i| primes[(i + 5) % primes.len()]).collect()
        }
        5 => {
            // Hard NO: a[i] = lcm(2..=i+2)
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for i in 0..n {
                let mut lcm: i64 = 1;
                for d in 2..=(i + 2) as i64 {
                    let g = gcd(lcm, d);
                    if let Some(prod) = (lcm / g).checked_mul(d) {
                        if prod <= 1_000_000_000 { lcm = prod; } else { lcm = 1_000_000_000; break; }
                    } else { lcm = 1_000_000_000; break; }
                }
                v.push(lcm);
            }
            v
        }
        6 => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
        7 => {
            let n = 100;
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
        8 => {
            let n = rng.gen_range_usize(1, 30);
            (0..n).map(|_| 2_i64.pow(rng.gen_range_usize(0, 29) as u32)).collect()
        }
        9 => {
            let n = rng.gen_range_usize(1, 30);
            let p: i64 = 1_000_000_007;
            (0..n).map(|_| p).collect()
        }
        _ => {
            let n = rng.gen_range_usize(1, 30);
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
    }
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

fn main() {
    let mut rng = Rng::new(1);
    let modes = 10usize;
    let total = 200usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut idx = 0;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 10) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(make_test(&mut rng, mode));
        }
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|a| Solution::can_erase_all(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
