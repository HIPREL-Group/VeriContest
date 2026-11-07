use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_bottles: i32, seed_exchange: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_bottles <= 100,
        2 <= seed_exchange <= 100,
    ensures
        1 <= res.0 <= 100,
        2 <= res.1 <= 100,
{
    let num_bottles = if mutation_kind == 0 {
        seed_bottles                                      // identity
    } else if mutation_kind == 1 && seed_bottles < 100 {
        seed_bottles + 1                                  // nudge up
    } else if mutation_kind == 2 && seed_bottles > 1 {
        seed_bottles - 1                                  // nudge down
    } else if mutation_kind == 3 {
        if seed_bottles <= 50 {
            seed_bottles * 2                              // double
        } else {
            seed_bottles
        }
    } else if mutation_kind == 4 {
        seed_bottles / 2 + 1                              // halve (stay >= 1)
    } else if mutation_kind == 5 {
        1                                                 // min boundary
    } else if mutation_kind == 6 {
        100                                               // max boundary
    } else if mutation_kind == 7 {
        101 - seed_bottles                                // mirror around 50
    } else {
        seed_bottles                                      // fallback
    };

    let num_exchange = if mutation_kind == 8 && seed_exchange < 100 {
        seed_exchange + 1                                 // nudge up
    } else if mutation_kind == 9 && seed_exchange > 2 {
        seed_exchange - 1                                 // nudge down
    } else if mutation_kind == 10 {
        2                                                 // min boundary
    } else if mutation_kind == 11 {
        100                                               // max boundary
    } else if mutation_kind == 12 {
        if seed_exchange <= 50 {
            seed_exchange * 2                             // double
        } else {
            seed_exchange
        }
    } else if mutation_kind == 13 {
        seed_exchange / 2 + 1                             // halve (stay >= 2) — note: min is 2, seed/2+1 >= 1+1=2
    } else if mutation_kind == 14 {
        102 - seed_exchange                               // mirror around 51
    } else {
        seed_exchange                                     // fallback (identity)
    };

    (num_bottles, num_exchange)
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
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 15;

    // Seed pool: examples from description + boundaries + interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (9, 3), (15, 4),                                // examples from description
        (1, 2), (1, 100), (100, 2), (100, 100),         // corner cases
        (1, 3), (2, 2), (2, 3), (3, 2),                 // small values
        (10, 2), (10, 3), (10, 5), (10, 10),            // num_bottles = 10
        (50, 2), (50, 5), (50, 10), (50, 50),           // num_bottles = 50
        (99, 2), (99, 3), (99, 99), (99, 100),          // near max bottles
        (100, 3), (100, 10), (100, 50),                 // max bottles
        (5, 5), (5, 6), (3, 4), (7, 8),                 // bottles < exchange
        (20, 7), (30, 11), (42, 13), (77, 23),          // varied
    ];

    // Seed pool × mutation_kind
    for &(sb, se) in &seeds {
        for mk in 0..num_mutations {
            if count >= count_goal { break; }
            let (nb, ne) = generate_test_case(sb, se, mk);
            if seen.insert((nb, ne)) {
                let result = Solution::num_water_bottles(nb, ne);
                writeln!(out, "{}", json!({
                    "input": {"numBottles": nb, "numExchange": ne},
                    "output": result
                })).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_goal {
        let sb = rng.gen_range_i64(1, 100) as i32;
        let se = rng.gen_range_i64(2, 100) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (nb, ne) = generate_test_case(sb, se, mk);
        if seen.insert((nb, ne)) {
            let result = Solution::num_water_bottles(nb, ne);
            writeln!(out, "{}", json!({
                "input": {"numBottles": nb, "numExchange": ne},
                "output": result
            })).unwrap();
            count += 1;
        }
    }
}
