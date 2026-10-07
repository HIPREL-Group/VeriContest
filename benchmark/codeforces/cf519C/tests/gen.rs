use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i64, seed_m: i64, mutation_kind: u8) -> (result: (i64, i64))
    requires
        0 <= seed_n <= 500000,
        0 <= seed_m <= 500000,
    ensures
        0 <= result.0 <= 500000,
        0 <= result.1 <= 500000,
{
    if mutation_kind == 0 {
        // identity
        (seed_n, seed_m)
    } else if mutation_kind == 1 && seed_n < 500000 {
        // nudge n up
        (seed_n + 1, seed_m)
    } else if mutation_kind == 2 && seed_n > 0 {
        // nudge n down
        (seed_n - 1, seed_m)
    } else if mutation_kind == 3 && seed_m < 500000 {
        // nudge m up
        (seed_n, seed_m + 1)
    } else if mutation_kind == 4 && seed_m > 0 {
        // nudge m down
        (seed_n, seed_m - 1)
    } else if mutation_kind == 5 {
        // n = 0
        (0, seed_m)
    } else if mutation_kind == 6 {
        // m = 0
        (seed_n, 0)
    } else if mutation_kind == 7 {
        // both zero
        (0, 0)
    } else if mutation_kind == 8 {
        // n = max
        (500000, seed_m)
    } else if mutation_kind == 9 {
        // m = max
        (seed_n, 500000)
    } else if mutation_kind == 10 {
        // both max
        (500000, 500000)
    } else if mutation_kind == 11 {
        // swap n and m
        (seed_m, seed_n)
    } else if mutation_kind == 12 {
        // n = m (equal)
        (seed_n, seed_n)
    } else if mutation_kind == 13 && seed_n <= 250000 {
        // double n
        (seed_n * 2, seed_m)
    } else if mutation_kind == 14 && seed_m <= 250000 {
        // double m
        (seed_n, seed_m * 2)
    } else if mutation_kind == 15 {
        // halve n
        (seed_n / 2, seed_m)
    } else if mutation_kind == 16 {
        // halve m
        (seed_n, seed_m / 2)
    } else {
        // fallback: identity
        (seed_n, seed_m)
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

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(519);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i64, m: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if n < 0 || n > 500_000 || m < 0 || m > 500_000 { return; }
        let key = format!("{}_{}", n, m);
        if !seen.insert(key) { return; }
        let result = Solution::max_training_teams(n, m);
        let inp = format!("{} {}\n", n, m);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(2, 6, &mut seen, &mut out, &mut count);
    emit(4, 5, &mut seen, &mut out, &mut count);

    emit(0, 0, &mut seen, &mut out, &mut count);
    emit(0, 500_000, &mut seen, &mut out, &mut count);
    emit(500_000, 0, &mut seen, &mut out, &mut count);
    emit(500_000, 500_000, &mut seen, &mut out, &mut count);
    emit(1, 1, &mut seen, &mut out, &mut count);
    emit(1, 2, &mut seen, &mut out, &mut count);
    emit(2, 1, &mut seen, &mut out, &mut count);
    emit(0, 1, &mut seen, &mut out, &mut count);
    emit(1, 0, &mut seen, &mut out, &mut count);
    emit(3, 3, &mut seen, &mut out, &mut count);
    emit(2, 4, &mut seen, &mut out, &mut count);
    emit(4, 2, &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = rng.gen_range_i64(0, 500_000);
        let m = rng.gen_range_i64(0, 500_000);
        emit(n, m, &mut seen, &mut out, &mut count);
    }
}

