use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        2 <= seed <= 30,
        (seed as int) % 2 == 0,
    ensures
        2 <= result <= 30,
        (result as int) % 2 == 0,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed <= 28 {
        seed + 2                                          // nudge up (stay even)
    } else if mutation_kind == 2 && seed >= 4 {
        seed - 2                                          // nudge down (stay even)
    } else if mutation_kind == 3 {
        2                                                 // min boundary
    } else if mutation_kind == 4 {
        30                                                // max boundary
    } else if mutation_kind == 5 {
        if seed <= 14 {
            seed * 2                                      // double (stay even, in range)
        } else {
            seed
        }
    } else if mutation_kind == 6 {
        // halve (only if result >= 2 and even)
        let h = seed / 2;
        if h >= 2 && h % 2 == 0 {
            h
        } else {
            seed
        }
    } else if mutation_kind == 7 {
        16                                                // middle value
    } else if mutation_kind == 8 {
        // complement: 32 - seed, which is even and in [2,30]
        let c = 32 - seed;
        if c >= 2 && c <= 30 {
            c
        } else {
            seed
        }
    } else {
        seed                                              // fallback
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

fn build_input(ns: &[i32]) -> String {
    let mut s = format!("{}\n", ns.len());
    for n in ns {
        s.push_str(&format!("{}\n", n));
    }
    s
}

fn build_output(ans: &[i64]) -> String {
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

    // Example
    {
        let ns = vec![2i32, 4];
        let answers: Vec<i64> = ns.iter().map(|&n| Solution::phoenix_balance_min_diff(n)).collect();
        let inp = build_input(&ns);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let all_evens: Vec<i32> = (1..=15).map(|i| 2 * i).collect();

    let mut count = 1usize;

    // Each single value
    for &n in &all_evens {
        if count >= target { break; }
        let ns = vec![n];
        let answers: Vec<i64> = ns.iter().map(|&n| Solution::phoenix_balance_min_diff(n)).collect();
        let inp = build_input(&ns);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    // Random bundles
    while count < target {
        let t: usize = if count < 30 { 1 } else { rng.gen_range_usize(2, 30) };
        let mut ns: Vec<i32> = Vec::new();
        for _ in 0..t {
            let n = (rng.gen_range_i64(1, 15) * 2) as i32;
            ns.push(n);
        }
        let answers: Vec<i64> = ns.iter().map(|&n| Solution::phoenix_balance_min_diff(n)).collect();
        let inp = build_input(&ns);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

