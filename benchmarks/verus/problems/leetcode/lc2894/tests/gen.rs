use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_n: i32,
    seed_m: i32,
    mutation_kind: u8,
) -> (result: (i32, i32))
    requires
        1 <= seed_n <= 1000,
        1 <= seed_m <= 1000,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= 1000,
{
    let n: i32;
    let m: i32;

    if mutation_kind == 0 {
        // identity
        n = seed_n;
        m = seed_m;
    } else if mutation_kind == 1 && seed_n < 1000 {
        // nudge n up
        n = seed_n + 1;
        m = seed_m;
    } else if mutation_kind == 2 && seed_n > 1 {
        // nudge n down
        n = seed_n - 1;
        m = seed_m;
    } else if mutation_kind == 3 && seed_m < 1000 {
        // nudge m up
        n = seed_n;
        m = seed_m + 1;
    } else if mutation_kind == 4 && seed_m > 1 {
        // nudge m down
        n = seed_n;
        m = seed_m - 1;
    } else if mutation_kind == 5 {
        // n = 1 (min boundary)
        n = 1;
        m = seed_m;
    } else if mutation_kind == 6 {
        // n = 1000 (max boundary)
        n = 1000;
        m = seed_m;
    } else if mutation_kind == 7 {
        // m = 1 (min boundary)
        n = seed_n;
        m = 1;
    } else if mutation_kind == 8 {
        // m = 1000 (max boundary)
        n = seed_n;
        m = 1000;
    } else if mutation_kind == 9 {
        // both boundaries: min n, max m
        n = 1;
        m = 1000;
    } else if mutation_kind == 10 {
        // both boundaries: max n, min m
        n = 1000;
        m = 1;
    } else if mutation_kind == 11 {
        // halve n
        n = if seed_n >= 2 { seed_n / 2 } else { seed_n };
        m = seed_m;
    } else if mutation_kind == 12 {
        // halve m
        n = seed_n;
        m = if seed_m >= 2 { seed_m / 2 } else { seed_m };
    } else if mutation_kind == 13 && seed_n <= 500 {
        // double n
        n = seed_n * 2;
        m = seed_m;
    } else if mutation_kind == 14 && seed_m <= 500 {
        // double m
        n = seed_n;
        m = seed_m * 2;
    } else if mutation_kind == 15 {
        // swap n and m
        n = seed_m;
        m = seed_n;
    } else {
        // fallback: identity
        n = seed_n;
        m = seed_m;
    }

    (n, m)
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![(10, 3), (5, 6), (5, 1), (5, 2)];

    for &(n, m) in &examples {
        if count >= goal { break; }
        if seen.insert((n, m)) {
            let output = Solution::difference_of_sums(n, m);
            writeln!(out, "{}", json!({"input": {"n": n, "m": m}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Boundary and interesting seed values
    let boundary_values: Vec<i32> = vec![1, 2, 3, 5, 10, 50, 100, 500, 999, 1000];

    // Generate boundary combinations
    for &bv_n in &boundary_values {
        for &bv_m in &boundary_values {
            if count >= goal { break; }
            if seen.insert((bv_n, bv_m)) {
                let output = Solution::difference_of_sums(bv_n, bv_m);
                writeln!(out, "{}", json!({"input": {"n": bv_n, "m": bv_m}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Random generation with mutations
    while count < goal {
        let seed_n = rng.gen_range_i64(1, 1000) as i32;
        let seed_m = rng.gen_range_i64(1, 1000) as i32;
        let mutation = rng.gen_u8() % 16;

        let (n, m) = generate_test_case(seed_n, seed_m, mutation);

        if seen.insert((n, m)) {
            let output = Solution::difference_of_sums(n, m);
            writeln!(out, "{}", json!({"input": {"n": n, "m": m}, "output": output})).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
