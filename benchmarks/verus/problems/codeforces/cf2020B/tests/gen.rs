use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u64, mutation_kind: u8) -> (result: u64)
    requires
        1 <= seed <= 1_000_000_000_000_000_000u64,
    ensures
        1 <= result <= 1_000_000_000_000_000_000u64,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < 1_000_000_000_000_000_000u64 {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed <= 500_000_000_000_000_000u64 {
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        let h = seed / 2;
        if h >= 1 {
            h                                             // halve
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        1u64                                              // min boundary
    } else if mutation_kind == 6 {
        1_000_000_000_000_000_000u64                      // max boundary
    } else if mutation_kind == 7 {
        if seed <= 999_999_999_999_999_999u64 {
            let s = seed + 1;
            if s <= 1_000_000_000_000_000_000u64 { s } else { seed }
        } else {
            seed
        }
    } else if mutation_kind == 8 {
        // clamp to mid-range
        if seed >= 500_000_000_000_000_000u64 {
            500_000_000_000_000_000u64
        } else {
            seed
        }
    } else {
        seed                                              // fallback
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

    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        let range = (hi - lo + 1) as u128;
        lo + (self.next_u64() as u128 % range) as u64
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

fn build_input(ks: &[u64]) -> String {
    let mut s = format!("{}\n", ks.len());
    for k in ks {
        s.push_str(&format!("{}\n", k));
    }
    s
}

fn build_output(answers: &[u64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
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

    let example: Vec<u64> = vec![1, 3, 8];
    {
        let answers: Vec<u64> = example.iter().map(|&k| Solution::min_bulbs_n(k)).collect();
        let inp = build_input(&example);
        let outp = build_output(&answers);
        let key = format!("{:?}", example);
        if seen.insert(key) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 10 { 1 }
                       else if count < 30 { rng.gen_range_usize(2, 5) }
                       else if count < 60 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };
        let mut ks: Vec<u64> = Vec::with_capacity(t);
        for _ in 0..t {
            let k = match rng.next_u64() % 4 {
                0 => rng.gen_range_u64(1, 100),
                1 => rng.gen_range_u64(1, 10_000),
                2 => rng.gen_range_u64(1, 1_000_000),
                _ => rng.gen_range_u64(1, 100_000_000),
            };
            ks.push(k);
        }
        let key = format!("{:?}", ks);
        if !seen.insert(key) { continue; }
        let answers: Vec<u64> = ks.iter().map(|&k| Solution::min_bulbs_n(k)).collect();
        let inp = build_input(&ks);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

