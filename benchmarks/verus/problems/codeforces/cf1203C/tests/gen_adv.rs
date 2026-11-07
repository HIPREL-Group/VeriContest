use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    fillers: &Vec<i64>,
) -> (result: (usize, Vec<i64>))
    requires
        1 <= n <= 400000,
        fillers.len() == n,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1000000000000i64,
    ensures
        result.0 == n,
        result.1.len() == n,
        1 <= result.0 <= 400000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1000000000000i64,
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            fillers.len() == n,
            forall|k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1000000000000i64,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1000000000000i64,
        decreases n - i,
    {
        let v = fillers[i];
        assert(1 <= v <= 1000000000000i64);
        a.push(v);
        i = i + 1;
    }
    (n, a)
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

fn build_input(a: &[i64]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i64) -> String { format!("{}\n", ans) }

fn random_array(rng: &mut Rng, len: usize, max_val: i64) -> Vec<i64> {
    (0..len).map(|_| rng.gen_range_i64(1, max_val)).collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64; h = h.wrapping_mul(1099511628211);
        for &x in &a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(&a);
        let ans = Solution::count_common_divisors(a.len(), a.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // High-divisor numbers (highly composite)
    let highly_composite: Vec<i64> = vec![
        1, 2, 6, 12, 24, 36, 48, 60, 120, 180, 240, 360, 720, 840, 1260, 1680, 2520,
        720_720, 720_720_000, 1_000_000_000_000,
    ];
    for &x in &highly_composite {
        emit(vec![x], &mut seen, &mut out, &mut count);
    }
    // pairs of these
    for &x in &highly_composite[..12] {
        for &y in &highly_composite[..12] {
            if count >= target { break; }
            emit(vec![x, y], &mut seen, &mut out, &mut count);
        }
    }
    // arrays with same value
    for &x in &highly_composite {
        for &n in &[1usize, 5, 100, 1000] {
            emit(vec![x; n], &mut seen, &mut out, &mut count);
        }
    }

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 50),
            2 => rng.gen_range_usize(50, 500),
            3 => rng.gen_range_usize(500, 5_000),
            4 => rng.gen_range_usize(5_000, 30_000),
            _ => rng.gen_range_usize(30_000, 100_000),
        };
        let max_val = match tries % 4 {
            0 => 10i64,
            1 => 1_000,
            2 => 1_000_000,
            _ => 1_000_000_000_000,
        };
        let v = random_array(&mut rng, n, max_val);
        emit(v, &mut seen, &mut out, &mut count);
    }
}

