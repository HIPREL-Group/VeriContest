use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i64,
    m: i64,
    t1: i32,
    y1: i64,
    t2: i32,
    y2: i64,
) -> (result: (i64, i64, i32, i64, i32, i64))
    requires
        1 <= n <= 1_000_000_000_000_000_000,
        1 <= m <= 1_000_000_000_000_000_000,
        t1 == 1 || t1 == 2,
        t2 == 1 || t2 == 2,
        t1 == 1 ==> 1 <= y1 <= n,
        t1 == 2 ==> 1 <= y1 <= m,
        t2 == 1 ==> 1 <= y2 <= n,
        t2 == 2 ==> 1 <= y2 <= m,
    ensures
        ({
            let (rn, rm, rt1, ry1, rt2, ry2) = result;
            &&& 1 <= rn <= 1_000_000_000_000_000_000
            &&& 1 <= rm <= 1_000_000_000_000_000_000
            &&& (rt1 == 1 || rt1 == 2)
            &&& (rt2 == 1 || rt2 == 2)
            &&& (rt1 == 1 ==> 1 <= ry1 <= rn)
            &&& (rt1 == 2 ==> 1 <= ry1 <= rm)
            &&& (rt2 == 1 ==> 1 <= ry2 <= rn)
            &&& (rt2 == 2 ==> 1 <= ry2 <= rm)
        }),
{
    (n, m, t1, y1, t2, y2)
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

fn build_input(n: i64, m: i64, queries: &[(i32,i64,i32,i64)]) -> String {
    let mut s = format!("{} {} {}\n", n, m, queries.len());
    for &(t1,y1,t2,y2) in queries {
        s.push_str(&format!("{} {} {} {}\n", t1, y1, t2, y2));
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

fn solve(n: i64, m: i64, queries: &[(i32,i64,i32,i64)]) -> Vec<bool> {
    queries.iter().map(|&(t1,y1,t2,y2)| Solution::corridor_same_component(n, m, t1, y1, t2, y2)).collect()
}

fn random_query(rng: &mut Rng, n: i64, m: i64) -> (i32, i64, i32, i64) {
    let t1: i32 = rng.gen_range_i64(1, 2) as i32;
    let y1: i64 = if t1 == 1 { rng.gen_range_i64(1, n) } else { rng.gen_range_i64(1, m) };
    let t2: i32 = rng.gen_range_i64(1, 2) as i32;
    let y2: i64 = if t2 == 1 { rng.gen_range_i64(1, n) } else { rng.gen_range_i64(1, m) };
    (t1, y1, t2, y2)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: i64, m: i64, queries: Vec<(i32,i64,i32,i64)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= n as u64; h = h.wrapping_mul(1099511628211);
        h ^= m as u64; h = h.wrapping_mul(1099511628211);
        h ^= queries.len() as u64; h = h.wrapping_mul(1099511628211);
        for &(t1,y1,t2,y2) in &queries {
            h ^= t1 as u64; h = h.wrapping_mul(1099511628211);
            h ^= y1 as u64; h = h.wrapping_mul(1099511628211);
            h ^= t2 as u64; h = h.wrapping_mul(1099511628211);
            h ^= y2 as u64; h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let answers = solve(n, m, &queries);
        let inp = build_input(n, m, &queries);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Coprime cases (all NO when crossing)
    let primes = vec![1i64, 2, 3, 5, 7, 11, 13, 100, 1009, 1_000_000_007, 999_999_999_989_i64];
    for &p in &primes {
        for &q in &primes {
            if count >= target { break; }
            let mut queries = Vec::new();
            queries.push((1, 1i64, 2, 1i64));
            if p > 1 { queries.push((1, p, 2, 1)); }
            if q > 1 { queries.push((2, q, 1, 1)); }
            if p > 1 && q > 1 { queries.push((1, p, 2, q)); }
            emit(p, q, queries, &mut seen, &mut out, &mut count);
        }
    }

    // Same n=m
    for &x in &[1i64, 2, 6, 12, 100, 1_000_000_007, 999_999_999_999_999_999_i64] {
        let queries: Vec<_> = (0..10).map(|_| random_query(&mut rng, x, x)).collect();
        emit(x, x, queries, &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 10000 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_i64(1, 10),
            1 => rng.gen_range_i64(1, 1000),
            2 => rng.gen_range_i64(1, 1_000_000_000),
            3 => rng.gen_range_i64(1, 999_999_999_999_999_999_i64),
            _ => rng.gen_range_i64(1, 1_000_000_000_000_000_000),
        };
        let m = match tries % 4 {
            0 => rng.gen_range_i64(1, 100),
            1 => rng.gen_range_i64(1, 1_000_000),
            2 => rng.gen_range_i64(1, 1_000_000_000_000),
            _ => rng.gen_range_i64(1, 1_000_000_000_000_000_000),
        };
        let q = match tries % 4 {
            0 => 1,
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 100),
            _ => rng.gen_range_usize(100, 1000),
        };
        let queries: Vec<_> = (0..q).map(|_| random_query(&mut rng, n, m)).collect();
        emit(n, m, queries, &mut seen, &mut out, &mut count);
    }
}

