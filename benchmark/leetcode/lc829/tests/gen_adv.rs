use vstd::prelude::*;

verus! {

pub fn generate_test_case(high: i32, low: i32) -> (n: i32)
    requires
        0 <= high <= 999_999,
        1 <= low <= 1000,
    ensures
        1 <= n <= 1_000_000_000,
{
    let n = high * 1000 + low;
    assert(n >= 1) by {
        assert(high * 1000 >= 0);
        assert(low >= 1);
    }
    assert(n <= 1_000_000_000) by {
        assert(high * 1000 <= 999_999 * 1000);
        assert(999_999 * 1000 == 999_999_000);
        assert(low <= 1000);
        assert(n <= 999_999_000 + 1000);
        assert(999_999_000 + 1000 == 1_000_000_000);
    }
    n
}

} // verus!

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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<i32> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: i32, seen: &mut HashSet<i32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 1 || n > 1_000_000_000 { return; }
        if !seen.insert(n) { return; }
        let result = Solution::consecutive_numbers_sum(n);
        writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
        *count += 1;
    };

    // Edge: small values
    for n in 1i32..=30 {
        emit(n, &mut seen, &mut out, &mut count);
    }

    // Edge: triangular numbers k*(k+1)/2 (always have many representations)
    let mut k: i64 = 1;
    while k * (k + 1) / 2 <= 1_000_000_000 {
        emit((k * (k + 1) / 2) as i32, &mut seen, &mut out, &mut count);
        // also +/- 1
        let t = k * (k + 1) / 2;
        if t > 1 { emit((t - 1) as i32, &mut seen, &mut out, &mut count); }
        if t < 1_000_000_000 { emit((t + 1) as i32, &mut seen, &mut out, &mut count); }
        k += 1;
        if k > 200 { break; }
    }

    // Edge: powers of 2 (always exactly 1 representation: just n itself)
    let mut p: i64 = 1;
    while p <= 1_000_000_000 {
        emit(p as i32, &mut seen, &mut out, &mut count);
        if p > 1 { emit((p - 1) as i32, &mut seen, &mut out, &mut count); }
        p *= 2;
    }

    // Edge: products of small odd primes (many divisors -> many representations)
    let bases: &[i32] = &[3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 315, 945, 3465, 45045];
    for &b in bases {
        let mut m: i64 = b as i64;
        while m <= 1_000_000_000 {
            emit(m as i32, &mut seen, &mut out, &mut count);
            m *= 2;
        }
        let mut m: i64 = b as i64;
        while m <= 1_000_000_000 {
            emit(m as i32, &mut seen, &mut out, &mut count);
            m *= 3;
        }
    }

    // Edge: known large primes (only 1 representation)
    for &n in &[
        999_999_937i32, 999_999_893, 999_999_751, 999_999_739,
        999_983, 999_961, 100_003, 99_991, 9973, 997, 97, 13, 11, 7, 5, 3, 2, 1,
    ] {
        emit(n, &mut seen, &mut out, &mut count);
    }

    // Edge: highly composite numbers
    for &n in &[
        720_720i32, 360_360, 277_200, 166_320, 110_880, 55_440, 27_720, 5040,
        2520, 1680, 1260, 720, 360, 240, 180, 120, 60, 48, 36, 24, 12, 6,
    ] {
        emit(n, &mut seen, &mut out, &mut count);
    }

    // Boundary
    for &n in &[1i32, 2, 999_999_999, 1_000_000_000] {
        emit(n, &mut seen, &mut out, &mut count);
    }

    // Random fill
    let mut tries = 0usize;
    while count < target && tries < 5000 {
        tries += 1;
        let n = match rng.next_u64() % 5 {
            0 => rng.gen_range_i32(1, 100),
            1 => rng.gen_range_i32(1, 10_000),
            2 => rng.gen_range_i32(1, 1_000_000),
            3 => rng.gen_range_i32(1, 100_000_000),
            _ => rng.gen_range_i32(1, 1_000_000_000),
        };
        emit(n, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} adversarial test cases", count);
}
