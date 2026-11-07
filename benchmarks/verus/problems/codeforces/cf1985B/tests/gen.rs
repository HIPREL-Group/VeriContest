use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed: i32,
    mutation_kind: u8,
) -> (result: i32)
    requires
        2i32 <= seed <= 100i32,
    ensures
        2 <= result <= 100,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 100 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 2 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // halve (clamped to min 2)
        let h = seed / 2;
        if h >= 2 { h } else { 2 }
    } else if mutation_kind == 4 && seed <= 50 {
        // double (clamped to max 100)
        seed * 2
    } else if mutation_kind == 5 {
        // min boundary
        2
    } else if mutation_kind == 6 {
        // max boundary
        100
    } else if mutation_kind == 7 {
        // midpoint
        51
    } else if mutation_kind == 8 {
        // complement: 102 - seed
        102 - seed
    } else {
        // fallback: identity
        seed
    }
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
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

fn build_input_multi(ns: &[i32]) -> String {
    let mut s = format!("{}\n", ns.len());
    for n in ns {
        s.push_str(&format!("{}\n", n));
    }
    s
}

fn build_output_multi(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    // examples first as t=1
    let example_pairs: Vec<Vec<i32>> = vec![
        vec![3, 15],
        vec![2],
        vec![100],
    ];
    for ex in &example_pairs {
        if count >= target { break; }
        let key = format!("{:?}", ex);
        if !seen.insert(key) { continue; }
        let answers: Vec<i32> = ex.iter().map(|&n| Solution::max_multiples_sum_x(n)).collect();
        let inp = build_input_multi(ex);
        let outp = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 10 { 1 }
                       else if count < 30 { rng.gen_range_usize(2, 5) }
                       else if count < 60 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };
        let mut ns: Vec<i32> = Vec::with_capacity(t);
        for _ in 0..t {
            ns.push(rng.gen_range_i64(2, 100) as i32);
        }
        let key = format!("{:?}", ns);
        if !seen.insert(key) { continue; }
        let answers: Vec<i32> = ns.iter().map(|&n| Solution::max_multiples_sum_x(n)).collect();
        let inp = build_input_multi(&ns);
        let outp = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

