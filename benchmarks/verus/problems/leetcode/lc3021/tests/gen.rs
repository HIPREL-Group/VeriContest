use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_m: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 100000,
        1 <= seed_m <= 100000,
    ensures
        1 <= res.0 <= 100000,
        1 <= res.1 <= 100000,
{
    let n: i32 = if mutation_kind == 0 {
        seed_n
    } else if mutation_kind == 1 && seed_n < 100000 {
        seed_n + 1
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1
    } else if mutation_kind == 3 && seed_n >= 2 && seed_n <= 50000 {
        seed_n * 2
    } else if mutation_kind == 4 {
        if seed_n / 2 >= 1 { seed_n / 2 } else { 1 }
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        100000
    } else {
        seed_n
    };

    let m: i32 = if mutation_kind == 7 {
        seed_m
    } else if mutation_kind == 8 && seed_m < 100000 {
        seed_m + 1
    } else if mutation_kind == 9 && seed_m > 1 {
        seed_m - 1
    } else if mutation_kind == 10 {
        1
    } else if mutation_kind == 11 {
        100000
    } else if mutation_kind == 12 {
        // set m = n (same value)
        if seed_n >= 1 && seed_n <= 100000 { seed_n } else { seed_m }
    } else {
        seed_m
    };

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
    let num_mutations: u8 = 13;

    // Example inputs from description
    let examples: Vec<(i32, i32)> = vec![
        (3, 2),
        (1, 1),
    ];
    for &(n, m) in &examples {
        if count >= target_count { break; }
        if seen.insert((n, m)) {
            let result = Solution::flower_game(n, m);
            writeln!(out, "{}", json!({"input": {"n": n, "m": m}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool with boundary and interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 100000), (100000, 1), (100000, 100000),
        (1, 2), (2, 1), (2, 2), (3, 3), (4, 4),
        (10, 10), (50, 50), (100, 100), (1000, 1000),
        (10000, 10000), (50000, 50000), (99999, 99999),
        (1, 50000), (50000, 1), (2, 99999), (99999, 2),
        (12345, 67890), (1, 3), (3, 1), (7, 13),
    ];

    // Seed pool × mutation_kind
    for &(sn, sm) in &seeds {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (n, m) = generate_test_case(sn, sm, mk);
            if seen.insert((n, m)) {
                let result = Solution::flower_game(n, m);
                writeln!(out, "{}", json!({"input": {"n": n, "m": m}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let sn = rng.gen_range_i64(1, 100000) as i32;
        let sm = rng.gen_range_i64(1, 100000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, m) = generate_test_case(sn, sm, mk);
        if seen.insert((n, m)) {
            let result = Solution::flower_game(n, m);
            writeln!(out, "{}", json!({"input": {"n": n, "m": m}, "output": result})).unwrap();
            count += 1;
        }
    }
}
