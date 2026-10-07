use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i64, b: i64, k: i64) -> (result: (i64, i64, i64))
    requires
        1 <= a <= 1_000_000_000,
        1 <= b <= 1_000_000_000,
        1 <= k <= 1_000_000_000,
    ensures
        ({
            let (ra, rb, rk) = result;
            1 <= ra <= 1_000_000_000
            && 1 <= rb <= 1_000_000_000
            && 1 <= rk <= 1_000_000_000
        }),
{
    (a, b, k)
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

fn build_input_multi(cases: &[(i64,i64,i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(a,b,k) in cases {
        s.push_str(&format!("{} {} {}\n", a, b, k));
    }
    s
}

fn build_output_multi(ans: &[i64]) -> String {
    let mut s = String::new();
    for a in ans {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |cases: Vec<(i64,i64,i64)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &(a,b,k) in &cases {
            h ^= a as u64; h = h.wrapping_mul(1099511628211);
            h ^= b as u64; h = h.wrapping_mul(1099511628211);
            h ^= k as u64; h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let answers: Vec<i64> = cases.iter().map(|&(a,b,k)| Solution::frog_position_after_jumps(a,b,k)).collect();
        let inp = build_input_multi(&cases);
        let outs = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundary cases with extreme values
    let m: i64 = 1_000_000_000;
    let bounds = vec![
        (1,1,1),
        (m,m,m),
        (m,1,m),
        (1,m,m),
        (m,m,1),
        (m-1,m,m),
        (m,1,2),
        (1,m,2),
    ];
    emit(bounds, &mut seen, &mut out, &mut count);

    // Sweep small a,b,k values
    let mut tries = 0;
    while count < target && tries < 10000 {
        tries += 1;
        let t: usize = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 1000),
        };
        let mut cases: Vec<(i64,i64,i64)> = Vec::new();
        for _ in 0..t {
            let max_v = match tries % 4 {
                0 => 10i64,
                1 => 1_000,
                2 => 1_000_000,
                _ => 1_000_000_000,
            };
            let a = rng.gen_range_i64(1, max_v);
            let b = rng.gen_range_i64(1, max_v);
            let k = rng.gen_range_i64(1, max_v);
            cases.push((a,b,k));
        }
        emit(cases, &mut seen, &mut out, &mut count);
    }
}

