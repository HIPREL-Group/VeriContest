use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i64, b: i64, n: i64, s: i64) -> (res: (i64, i64, i64, i64))
    ensures
        1 <= res.0 <= 1_000_000_000,
        1 <= res.1 <= 1_000_000_000,
        1 <= res.2 <= 1_000_000_000,
        1 <= res.3 <= 1_000_000_000,
{
    let a = if a < 1 { 1 } else if a > 1000000000 { 1000000000 } else { a };
    let b = if b < 1 { 1 } else if b > 1000000000 { 1000000000 } else { b };
    let n = if n < 1 { 1 } else if n > 1000000000 { 1000000000 } else { n };
    let s = if s < 1 { 1 } else if s > 1000000000 { 1000000000 } else { s };
    (a, b, n, s)
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

fn build_input(cases: &[(i64,i64,i64,i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(a,b,n,sv) in cases {
        s.push_str(&format!("{} {} {} {}\n", a, b, n, sv));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
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

    let mut emit = |cases: Vec<(i64,i64,i64,i64)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64; h = h.wrapping_mul(1099511628211);
        for &(a,b,n,sv) in &cases {
            h ^= a as u64; h = h.wrapping_mul(1099511628211);
            h ^= b as u64; h = h.wrapping_mul(1099511628211);
            h ^= n as u64; h = h.wrapping_mul(1099511628211);
            h ^= sv as u64; h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let answers: Vec<bool> = cases.iter().map(|&(a,b,n,sv)| Solution::payment_without_change(a,b,n,sv)).collect();
        let cases: Vec<_> = cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1, c.2, c.3)).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // boundary
    let m: i64 = 1_000_000_000;
    let extremes = vec![
        (1,1,1,1),
        (m,m,m,1),
        (m,m,m,m*m),
        (1,m,1,m+1),
        (m,1,1,m+1),
        (1,1,m,m),
    ];
    emit(extremes, &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let t: usize = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 1000),
        };
        let mut cases: Vec<(i64,i64,i64,i64)> = Vec::new();
        for _ in 0..t {
            let max_v = match tries % 4 {
                0 => 10i64,
                1 => 1000,
                2 => 1_000_000,
                _ => 1_000_000_000,
            };
            let a = rng.gen_range_i64(1, max_v);
            let b = rng.gen_range_i64(1, max_v);
            let n = rng.gen_range_i64(1, max_v);
            let max_s = (max_v.saturating_mul(1000)).min(1_000_000_000_000);
            let sv = rng.gen_range_i64(1, max_s);
            cases.push((a,b,n,sv));
        }
        emit(cases, &mut seen, &mut out, &mut count);
    }
}
