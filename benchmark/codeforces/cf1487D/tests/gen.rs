use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u64, mutation_kind: u8) -> (result: u64)
    requires
        1 <= seed <= 1_000_000_000u64,
    ensures
        1 <= result <= 1_000_000_000u64,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000u64 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1u64 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // halve (stays >= 1 since seed >= 1)
        let h = seed / 2;
        if h >= 1 {
            h
        } else {
            1u64
        }
    } else if mutation_kind == 4 && seed <= 500_000_000u64 {
        // double
        seed * 2
    } else if mutation_kind == 5 {
        // min boundary
        1u64
    } else if mutation_kind == 6 {
        // max boundary
        1_000_000_000u64
    } else if mutation_kind == 7 {
        // square root region (interesting for this problem)
        let s = seed / 1000;
        if s >= 1 {
            s
        } else {
            1u64
        }
    } else {
        // fallback: identity
        seed
    }
}

}

use std::io::Write;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        let r = hi - lo + 1;
        lo + self.next_u64() % r
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

fn build_input(ns: &[u64]) -> String {
    let mut s = format!("{}\n", ns.len());
    for n in ns {
        s.push_str(&format!("{}\n", n));
    }
    s
}

fn build_output(ans: &[u64]) -> String {
    let mut s = String::new();
    for a in ans {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Examples
    {
        let ns: Vec<u64> = vec![3, 6, 9];
        let answers: Vec<u64> = ns.iter().map(|&n| Solution::vasya_pythagorean_triples_count(n)).collect();
        let inp = build_input(&ns);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    let edges: Vec<u64> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 100, 1000, 10000, 1_000_000_000];
    for e in edges {
        if count >= target { break; }
        let ns = vec![e];
        let answers: Vec<u64> = ns.iter().map(|&n| Solution::vasya_pythagorean_triples_count(n)).collect();
        let inp = build_input(&ns);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 30) };
        let mut ns: Vec<u64> = Vec::new();
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => rng.gen_range_u64(1, 10),
                1 => rng.gen_range_u64(1, 100),
                2 => rng.gen_range_u64(1, 10000),
                3 => rng.gen_range_u64(1, 1_000_000),
                _ => rng.gen_range_u64(1, 1_000_000_000),
            };
            ns.push(n);
        }
        let answers: Vec<u64> = ns.iter().map(|&n| Solution::vasya_pythagorean_triples_count(n)).collect();
        let inp = build_input(&ns);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

