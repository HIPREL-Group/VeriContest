use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: i32, seed_b: i32, seed_c: i32, mutation_kind: u8) -> (res: (i32, i32, i32))
    ensures
        1 <= res.0 <= 1_000_000_000,
        1 <= res.1 <= 1_000_000_000,
        1 <= res.2 <= 1_000_000_000,
{
    let seed_a = if seed_a < 1 { 1 } else if seed_a > 1000000000 { 1000000000 } else { seed_a };
    let seed_b = if seed_b < 1 { 1 } else if seed_b > 1000000000 { 1000000000 } else { seed_b };
    let seed_c = if seed_c < 1 { 1 } else if seed_c > 1000000000 { 1000000000 } else { seed_c };
    let a = if mutation_kind == 0 {
        seed_a
    } else if mutation_kind == 1 && seed_a < 1_000_000_000 {
        seed_a + 1
    } else if mutation_kind == 2 && seed_a > 1 {
        seed_a - 1
    } else if mutation_kind == 3 && seed_a <= 500_000_000 {
        seed_a * 2
    } else if mutation_kind == 4 {
        let h = seed_a / 2;
        if h >= 1 { h } else { 1 }
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        1_000_000_000
    } else {
        seed_a
    };

    let b = if mutation_kind == 7 && seed_b < 1_000_000_000 {
        seed_b + 1
    } else if mutation_kind == 8 && seed_b > 1 {
        seed_b - 1
    } else if mutation_kind == 9 {
        // set b = a for interesting bit patterns
        a
    } else if mutation_kind == 10 && seed_b <= 500_000_000 {
        seed_b * 2
    } else {
        seed_b
    };

    let c = if mutation_kind == 11 && seed_c < 1_000_000_000 {
        seed_c + 1
    } else if mutation_kind == 12 && seed_c > 1 {
        seed_c - 1
    } else if mutation_kind == 13 {
        // c = a | b would be ideal but we can't compute bitwise OR in spec easily
        // instead set c = 1 (minimum)
        1
    } else if mutation_kind == 14 {
        1_000_000_000
    } else {
        seed_c
    };

    (a, b, c)
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 15;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (2, 6, 5),
        (4, 2, 7),
        (1, 2, 3),
    ];
    for (a, b, c) in &examples {
        if count >= target_count { break; }
        let result = Solution::min_flips(*a, *b, *c);
        writeln!(out, "{}", json!({"input": {"a": a, "b": b, "c": c}, "output": result})).unwrap();
        count += 1;
        seen.insert((*a as i64, *b as i64, *c as i64));
    }

    // Seed pool with interesting values
    let seed_vals: Vec<i32> = vec![
        1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 42, 100, 255, 256, 1023, 1024,
        1 << 15, 1 << 20, 1 << 29, 999_999_999, 1_000_000_000,
        0x5555_5555 & 0x3B9A_C9FF,  // alternating bits, clamped
        0x2AAA_AAAA,
    ];

    // Seed pool × mutation_kind
    for &sa in &seed_vals {
        for &sb in &seed_vals[..8] {
            for mk in 0..num_mutations {
                if count >= target_count { break; }
                let sc = sb;  // reuse as c seed
                let (a, b, c) = generate_test_case(sa, sb, sc, mk);
                if seen.insert((a as i64, b as i64, c as i64)) {
                    let result = Solution::min_flips(a, b, c);
                    writeln!(out, "{}", json!({"input": {"a": a, "b": b, "c": c}, "output": result})).unwrap();
                    count += 1;
                }
            }
        }
        if count >= target_count { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let sa = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let sb = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let sc = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (a, b, c) = generate_test_case(sa, sb, sc, mk);
        if seen.insert((a as i64, b as i64, c as i64)) {
            let result = Solution::min_flips(a, b, c);
            writeln!(out, "{}", json!({"input": {"a": a, "b": b, "c": c}, "output": result})).unwrap();
            count += 1;
        }
    }
}
