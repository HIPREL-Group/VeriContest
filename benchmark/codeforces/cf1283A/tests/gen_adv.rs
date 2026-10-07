use vstd::prelude::*;

verus! {

pub fn generate_test_case(h: i32, m: i32) -> (result: (i32, i32))
    requires
        0 <= h < 24,
        0 <= m < 60,
        !(h == 0 && m == 0),
    ensures
        ({
            let (rh, rm) = result;
            &&& 0 <= rh < 24
            &&& 0 <= rm < 60
            &&& !(rh == 0 && rm == 0)
        }),
{
    (h, m)
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
        (lo as i64 + (self.next_u64() as u64 % r) as i64) as i32
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

fn build_input(cases: &[(i32, i32)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(h, m) in cases { s.push_str(&format!("{} {}\n", h, m)); }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
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

    let mut emit = |cases: Vec<(i32,i32)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if cases.iter().any(|&(h,m)| h == 0 && m == 0) { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64; h = h.wrapping_mul(1099511628211);
        for &(hh,mm) in &cases {
            h ^= hh as u64; h = h.wrapping_mul(1099511628211);
            h ^= mm as u64; h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let answers: Vec<i32> = cases.iter().map(|&(h,m)| Solution::minutes_before_new_year_one(h,m)).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Comprehensive coverage of (h, m)
    let mut all_pairs: Vec<(i32,i32)> = Vec::new();
    for h in 0..24 {
        for m in 0..60 {
            if !(h == 0 && m == 0) { all_pairs.push((h,m)); }
        }
    }
    // Big bundles
    for chunk in all_pairs.chunks(100) {
        emit(chunk.to_vec(), &mut seen, &mut out, &mut count);
    }
    // Single all
    emit(all_pairs.clone(), &mut seen, &mut out, &mut count);
    // Pairs of edge cases
    emit(vec![(0,1),(23,59),(0,1),(23,59)], &mut seen, &mut out, &mut count);
    emit(vec![(12,0),(12,1),(12,30),(12,59)], &mut seen, &mut out, &mut count);

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
        let mut cases: Vec<(i32,i32)> = Vec::new();
        for _ in 0..t {
            let h = rng.gen_range_i32(0, 23);
            let m = rng.gen_range_i32(0, 59);
            if h == 0 && m == 0 { continue; }
            cases.push((h,m));
        }
        if !cases.is_empty() {
            emit(cases, &mut seen, &mut out, &mut count);
        }
    }
}

