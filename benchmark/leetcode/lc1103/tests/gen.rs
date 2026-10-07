use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_candies: i32, seed_people: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_candies <= 1_000_000_000,
        1 <= seed_people <= 1000,
    ensures
        1 <= res.0 <= 1_000_000_000,
        1 <= res.1 <= 1000,
{
    let candies: i32 = if mutation_kind == 0 {
        // identity
        seed_candies
    } else if mutation_kind == 1 && seed_candies < 1_000_000_000 {
        // nudge up
        seed_candies + 1
    } else if mutation_kind == 2 && seed_candies > 1 {
        // nudge down
        seed_candies - 1
    } else if mutation_kind == 3 && seed_candies <= 500_000_000 {
        // double
        seed_candies * 2
    } else if mutation_kind == 4 {
        // halve (at least 1)
        let h = seed_candies / 2;
        if h < 1 { 1 } else { h }
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        1_000_000_000
    } else if mutation_kind == 7 {
        // small value
        if seed_people as i32 <= 1_000_000_000 { seed_people as i32 } else { seed_candies }
    } else {
        seed_candies
    };

    let num_people: i32 = if mutation_kind == 8 && seed_people < 1000 {
        // nudge people up
        seed_people + 1
    } else if mutation_kind == 9 && seed_people > 1 {
        // nudge people down
        seed_people - 1
    } else if mutation_kind == 10 {
        // min people
        1
    } else if mutation_kind == 11 {
        // max people
        1000
    } else if mutation_kind == 12 && seed_people <= 500 {
        // double people
        seed_people * 2
    } else {
        seed_people
    };

    (candies, num_people)
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
    let mut count = 0usize;
    let num_mutations: u8 = 13;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (7, 4),
        (10, 3),
    ];
    for (c, n) in &examples {
        if count >= target_count { break; }
        if seen.insert((*c as i64, *n as i64)) {
            let result = Solution::distribute_candies(*c, *n);
            writeln!(out, "{}", json!({"input": {"candies": c, "num_people": n}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: interesting candies × interesting people counts
    let candies_seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 10, 15, 100, 1000, 10000, 100000,
        1_000_000, 10_000_000, 100_000_000, 500_000_000, 999_999_999, 1_000_000_000,
    ];
    let people_seeds: Vec<i32> = vec![
        1, 2, 3, 4, 5, 10, 50, 100, 500, 999, 1000,
    ];

    // Seed pool × mutation_kind
    for &sc in &candies_seeds {
        for &sp in &people_seeds {
            for mk in 0..num_mutations {
                if count >= target_count { break; }
                let (candies, num_people) = generate_test_case(sc, sp, mk);
                if seen.insert((candies as i64, num_people as i64)) {
                    let result = Solution::distribute_candies(candies, num_people);
                    writeln!(out, "{}", json!({"input": {"candies": candies, "num_people": num_people}, "output": result})).unwrap();
                    count += 1;
                }
            }
            if count >= target_count { break; }
        }
        if count >= target_count { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        // Diverse size classes for candies
        let sc = match count % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,           // tiny
            1 => rng.gen_range_i64(1, 1000) as i32,         // small
            2 => rng.gen_range_i64(1000, 100000) as i32,    // medium
            3 => rng.gen_range_i64(100000, 10_000_000) as i32, // large
            _ => rng.gen_range_i64(10_000_000, 1_000_000_000) as i32, // max
        };
        let sp = match count % 4 {
            0 => rng.gen_range_i64(1, 5) as i32,
            1 => rng.gen_range_i64(1, 50) as i32,
            2 => rng.gen_range_i64(50, 500) as i32,
            _ => rng.gen_range_i64(500, 1000) as i32,
        };
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (candies, num_people) = generate_test_case(sc, sp, mk);
        if seen.insert((candies as i64, num_people as i64)) {
            let result = Solution::distribute_candies(candies, num_people);
            writeln!(out, "{}", json!({"input": {"candies": candies, "num_people": num_people}, "output": result})).unwrap();
            count += 1;
        }
    }
}
