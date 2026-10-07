use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i64, seed_k: i64, mutation_kind: u8) -> (result: (i64, i64))
    requires
        1 <= seed_n <= 1_000_000_000,
        1 <= seed_k <= seed_n,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= result.0,
{
    let n: i64;
    let k: i64;

    if mutation_kind == 0 {
        // identity
        n = seed_n;
        k = seed_k;
    } else if mutation_kind == 1 && seed_n < 1_000_000_000 {
        // nudge n up, clamp k
        n = seed_n + 1;
        k = seed_k;
    } else if mutation_kind == 2 && seed_n > 1 && seed_k < seed_n {
        // nudge n down (only if k still fits)
        n = seed_n - 1;
        k = seed_k;
    } else if mutation_kind == 3 && seed_k < seed_n {
        // nudge k up
        n = seed_n;
        k = seed_k + 1;
    } else if mutation_kind == 4 && seed_k > 1 {
        // nudge k down
        n = seed_n;
        k = seed_k - 1;
    } else if mutation_kind == 5 {
        // k = 1 (minimum k)
        n = seed_n;
        k = 1;
    } else if mutation_kind == 6 {
        // k = n (maximum k)
        n = seed_n;
        k = seed_n;
    } else if mutation_kind == 7 {
        // n = 1, k = 1 (minimum case)
        n = 1;
        k = 1;
    } else if mutation_kind == 8 {
        // n = max boundary
        n = 1_000_000_000;
        k = seed_k;
    } else if mutation_kind == 9 {
        // n = max, k = max
        n = 1_000_000_000;
        k = 1_000_000_000;
    } else if mutation_kind == 10 {
        // n = max, k = 1
        n = 1_000_000_000;
        k = 1;
    } else if mutation_kind == 11 && seed_n <= 500_000_000 {
        // double n, keep k
        n = seed_n * 2;
        k = seed_k;
    } else if mutation_kind == 12 {
        // halve n, clamp k
        let half_n = if seed_n / 2 >= 1 { seed_n / 2 } else { 1i64 };
        n = half_n;
        k = if seed_k <= half_n { seed_k } else { half_n };
    } else if mutation_kind == 13 {
        // k = n / 2 (midpoint)
        let half = if seed_n / 2 >= 1 { seed_n / 2 } else { 1i64 };
        n = seed_n;
        k = half;
    } else {
        // fallback: identity
        n = seed_n;
        k = seed_k;
    }

    (n, k)
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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

fn build_input(cases: &[(i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(n, k) in cases {
        s.push_str(&format!("{} {}\n", n, k));
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
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let example: Vec<(i64, i64)> = vec![
        (1, 1), (2, 1), (2, 2), (3, 2), (4, 4),
    ];
    {
        let answers: Vec<bool> = example.iter().map(|&(n, k)| Solution::major_oak_leaves_even(n, k)).collect();
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
        let mut cases: Vec<(i64, i64)> = Vec::with_capacity(t);
        for _ in 0..t {
            let n = match rng.next_u64() % 4 {
                0 => rng.gen_range_i64(1, 10),
                1 => rng.gen_range_i64(1, 1000),
                2 => rng.gen_range_i64(1, 1_000_000),
                _ => rng.gen_range_i64(1, 1_000_000_000),
            };
            let k = rng.gen_range_i64(1, n);
            cases.push((n, k));
        }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<bool> = cases.iter().map(|&(n, k)| Solution::major_oak_leaves_even(n, k)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

