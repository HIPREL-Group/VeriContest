use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: i128, seed_b: i128) -> (result: (i128, i128))
    requires
        seed_a >= 1,
        seed_b >= 1,
        seed_a <= 1000000000000000000,
        seed_b <= 1000000000000000000,
        (seed_a as int) * (seed_b as int) <= 1000000000000000000,
    ensures
        result.0 >= 1,
        result.1 >= 1,
        result.0 <= 1000000000000000000,
        result.1 <= 1000000000000000000,
        (result.0 as int) * (result.1 as int) <= 1000000000000000000,
{
    (seed_a, seed_b)
}

}

extern crate serde_json;
use serde_json::json;
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    // code.rs iterates k from 1..=b, so cap b for runtime
    let max_b: i128 = 500_000;
    let max_val: i128 = 1_000_000_000_000_000_000;
    let target: usize = 200;

    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<(i128, i128)> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: i128, b: i128,
                    seen: &mut HashSet<(i128, i128)>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target { return; }
        if a < 1 || b < 1 || a > max_val || b > max_val { return; }
        if a.checked_mul(b).map_or(true, |p| p > max_val) { return; }
        if b > max_b { return; }
        if !seen.insert((a, b)) { return; }
        let result = Solution::maximum_even_sum(a, b);
        let inp_str = format!("1\n{} {}\n", a, b);
        let out_str = format!("{}\n", result);
        writeln!(out, "{}", json!({"input": inp_str, "output": out_str})).unwrap();
        *count += 1;
    };

    // Examples from description
    emit(1, 1, &mut seen, &mut out, &mut count);
    emit(1, 4, &mut seen, &mut out, &mut count);
    emit(2, 4, &mut seen, &mut out, &mut count);

    // Edge: parity boundaries
    let parity_seeds: &[(i128, i128)] = &[
        (1, 1), (1, 2), (2, 1), (2, 2),
        (1, 3), (3, 1), (3, 3),
        (1, 5), (5, 1), (5, 5),
        (2, 3), (3, 2),
        (1, 7), (7, 1), (7, 7),
        (1, 8), (8, 1),
        (1, 9), (9, 1), (9, 9),
        (2, 5), (5, 2), (2, 7), (7, 2),
        (3, 4), (4, 3), (4, 4),
        (6, 6), (12, 12), (24, 24),
        (1, 100), (100, 1), (100, 100),
        (1, 999), (999, 1), (999, 999),
        (1, 1000), (1000, 1),
    ];
    for &(a, b) in parity_seeds {
        emit(a, b, &mut seen, &mut out, &mut count);
    }

    // Edge: powers of 2 for b (many divisors)
    let pow2: &[i128] = &[1, 2, 4, 8, 16, 32, 64, 128, 256, 1024, 4096, 65_536, 262_144];
    for &b in pow2 {
        for &a in &[1i128, 2, 3, 5, 7, 11, 13, 100, 999, 1_000_000, 1_000_000_000] {
            emit(a, b, &mut seen, &mut out, &mut count);
        }
    }

    // Edge: highly composite b
    let hcn: &[i128] = &[12, 24, 36, 48, 60, 120, 360, 720, 2520, 5040, 27720, 55440, 277200];
    for &b in hcn {
        for &a in &[1i128, 2, 3, 7, 100, 1_000_000_000] {
            emit(a, b, &mut seen, &mut out, &mut count);
        }
    }

    // Edge: prime b
    let primes: &[i128] = &[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 97, 257, 1009, 99991, 499979];
    for &b in primes {
        for &a in &[1i128, 2, 3, 100, 999_999_999, 1_000_000_000_000_000_000] {
            emit(a, b, &mut seen, &mut out, &mut count);
        }
    }

    // Edge: large a, small b
    for &a in &[
        500_000_000_000_000_000i128,
        999_999_999_999_999_999,
        1_000_000_000_000_000_000,
        500_000_000_000_000_001,
    ] {
        for &b in &[1i128, 2] {
            emit(a, b, &mut seen, &mut out, &mut count);
        }
    }

    // Edge: small a, b that maximizes divisor count under runtime cap
    for &a in &[1i128, 2, 3, 5, 6, 7] {
        for &b in &[
            120i128, 360, 720, 2520, 5040, 27720, 55440,
            166_320, 277_200, 498_960,
        ] {
            emit(a, b, &mut seen, &mut out, &mut count);
        }
    }

    // Edge: a*b near 10^18 boundary (with capped b)
    for &a in &[
        2_000_000_000_000i128,
        2_000_000_000_000_000,
        500_000_000_000_000,
    ] {
        let b_cap = (max_val / a).min(max_b);
        if b_cap >= 1 { emit(a, b_cap, &mut seen, &mut out, &mut count); }
        if b_cap >= 2 { emit(a, b_cap - 1, &mut seen, &mut out, &mut count); }
    }

    // Edge: both odd
    for &a in &[1i128, 3, 5, 7, 9, 11, 13, 15, 99, 999, 9999, 999_999_999_999_999_999] {
        for &b in &[1i128, 3, 5, 7, 9, 11, 13, 15, 99, 999, 4999] {
            emit(a, b, &mut seen, &mut out, &mut count);
        }
    }

    // Edge: a even, b odd (and vice versa)
    for &a in &[2i128, 4, 8, 16, 100, 1_000_000_000_000_000] {
        for &b in &[1i128, 3, 5, 7, 99, 999, 9999, 99991] {
            emit(a, b, &mut seen, &mut out, &mut count);
        }
    }

    // Random adversarial fill
    let mut tries = 0usize;
    while count < target && tries < 10_000 {
        tries += 1;
        let seed_a = match rng.next_u64() % 6 {
            0 => rng.gen_range_i64(1, 10) as i128,
            1 => rng.gen_range_i64(1, 1000) as i128,
            2 => rng.gen_range_i64(1, 1_000_000) as i128,
            3 => rng.gen_range_i64(1, 1_000_000_000) as i128,
            4 => rng.gen_range_i64(1_000_000_000, 1_000_000_000_000) as i128,
            _ => rng.gen_range_i64(1, max_val as i64) as i128,
        };
        let b_limit = (max_val / seed_a).min(max_b);
        if b_limit < 1 { continue; }
        let seed_b = rng.gen_range_i64(1, b_limit as i64) as i128;
        emit(seed_a, seed_b, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} adversarial test cases", count);
}
