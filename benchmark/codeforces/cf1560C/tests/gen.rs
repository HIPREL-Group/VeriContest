use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i64, mutation_kind: u8) -> (result: i64)
    requires
        1 <= seed <= 1_000_000_000i64,
    ensures
        1 <= result <= 1_000_000_000i64,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000i64 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // halve (stays >= 1)
        let h = seed / 2;
        if h < 1 { 1i64 } else { h }
    } else if mutation_kind == 4 {
        // double (clamped to max)
        if seed <= 500_000_000 {
            seed * 2
        } else {
            1_000_000_000i64
        }
    } else if mutation_kind == 5 {
        // min boundary
        1i64
    } else if mutation_kind == 6 {
        // max boundary
        1_000_000_000i64
    } else if mutation_kind == 7 {
        // scale down (interesting for sqrt region)
        let s = seed / 1000;
        if s < 1 { 1i64 } else { s }
    } else if mutation_kind == 8 {
        // third of value
        let t = seed / 3;
        if t < 1 { 1i64 } else { t }
    } else if mutation_kind == 9 {
        // complement within range: max - seed + 1
        1_000_000_000i64 - seed + 1
    } else {
        // fallback
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
    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
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



fn build_input(ks: &[i64]) -> String {
    let mut s = format!("{}\n", ks.len());
    for &k in ks { s.push_str(&format!("{}\n", k)); }
    s
}

fn build_output(answers: &[(i64, i64)]) -> String {
    let mut s = String::new();
    for &(r, c) in answers { s.push_str(&format!("{} {}\n", r, c)); }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let mut emit = |ks: Vec<i64>, count: &mut usize, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>| {
        if *count >= target { return; }
        let inp = build_input(&ks);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<(i64, i64)> = ks.iter().map(|&k| Solution::infinity_table_cell(k)).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples (combined as one multi-test)
    let examples: Vec<i64> = vec![11, 14, 5, 4, 1, 2, 1_000_000_000];
    emit(examples.clone(), &mut count, &mut seen, &mut out);
    // Each example as standalone
    for &k in &examples { emit(vec![k], &mut count, &mut seen, &mut out); }

    // Interesting seeds
    let interesting_seeds: Vec<i64> = vec![
        1, 2, 3, 4, 5, 8, 9, 10, 15, 16, 17, 24, 25, 26,
        35, 36, 37, 48, 49, 50, 99, 100, 101,
        999, 1000, 1001, 9999, 10000, 10001,
        999_999_999, 1_000_000_000,
    ];
    let mut buf: Vec<i64> = Vec::new();
    let mut bundle_size: usize = 1;
    for &s in &interesting_seeds {
        for mk in 0..=10u8 {
            let k = generate_test_case(s, mk);
            buf.push(k);
            if buf.len() >= bundle_size {
                emit(buf.clone(), &mut count, &mut seen, &mut out);
                buf.clear();
                bundle_size = 1 + rng.gen_range_usize(0, 30);
            }
        }
    }
    if !buf.is_empty() { emit(buf.clone(), &mut count, &mut seen, &mut out); buf.clear(); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 50) };
        let mut ks: Vec<i64> = Vec::new();
        for _ in 0..t {
            let s = match rng.gen_u8() % 5 {
                0 => rng.gen_range_i64(1, 10),
                1 => rng.gen_range_i64(1, 1000),
                2 => rng.gen_range_i64(1000, 1_000_000),
                3 => rng.gen_range_i64(1_000_000, 1_000_000_000),
                _ => rng.gen_range_i64(1, 1_000_000_000),
            };
            let mk = rng.gen_u8() % 11;
            ks.push(generate_test_case(s, mk));
        }
        emit(ks, &mut count, &mut seen, &mut out);
    }
}

