use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_h: i32, seed_m: i32, mutation_kind: u8) -> (result: (i32, i32))
    requires
        0 <= seed_h < 24,
        0 <= seed_m < 60,
        !(seed_h == 0 && seed_m == 0),
    ensures
        0 <= result.0 < 24,
        0 <= result.1 < 60,
        !(result.0 == 0 && result.1 == 0),
{
    if mutation_kind == 0 {
        // identity
        (seed_h, seed_m)
    } else if mutation_kind == 1 && seed_h < 23 {
        // nudge h up
        (seed_h + 1, seed_m)
    } else if mutation_kind == 2 && seed_h > 0 {
        // nudge h down (if h-1==0 && m==0, keep original)
        if seed_h - 1 == 0 && seed_m == 0 {
            (seed_h, seed_m)
        } else {
            (seed_h - 1, seed_m)
        }
    } else if mutation_kind == 3 && seed_m < 59 {
        // nudge m up
        (seed_h, seed_m + 1)
    } else if mutation_kind == 4 && seed_m > 0 {
        // nudge m down (if h==0 && m-1==0, keep original)
        if seed_h == 0 && seed_m - 1 == 0 {
            (seed_h, seed_m)
        } else {
            (seed_h, seed_m - 1)
        }
    } else if mutation_kind == 5 {
        // set h to 0, keep m (if m==0, set m to 1)
        if seed_m == 0 {
            (0, 1i32)
        } else {
            (0, seed_m)
        }
    } else if mutation_kind == 6 {
        // set m to 0, keep h (if h==0, set h to 1)
        if seed_h == 0 {
            (1i32, 0)
        } else {
            (seed_h, 0)
        }
    } else if mutation_kind == 7 {
        // max h boundary
        (23, seed_m)
    } else if mutation_kind == 8 {
        // max m boundary
        (seed_h, 59)
    } else if mutation_kind == 9 {
        // both max boundaries
        (23, 59)
    } else if mutation_kind == 10 {
        // h=0, m=1 (near midnight)
        (0, 1i32)
    } else {
        // fallback
        (seed_h, seed_m)
    }
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
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    // Example
    let example = vec![(23,55),(23,0),(0,1),(4,20),(23,59)];
    emit(example, &mut seen, &mut out, &mut count);

    // Singletons
    emit(vec![(0,1)], &mut seen, &mut out, &mut count);
    emit(vec![(23,59)], &mut seen, &mut out, &mut count);
    emit(vec![(12,30)], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let t: usize = if tries < 5 { 1 } else { rng.gen_range_usize(2, 50) };
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

