use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_total: i32,
    seed_cost1: i32,
    seed_cost2: i32,
    mutation_kind: u8,
) -> (res: (i32, i32, i32))
    requires
        1 <= seed_total <= 1000000,
        1 <= seed_cost1 <= 1000000,
        1 <= seed_cost2 <= 1000000,
    ensures
        1 <= res.0 <= 1000000,
        1 <= res.1 <= 1000000,
        1 <= res.2 <= 1000000,
{
    let total = if mutation_kind == 0 {
        seed_total                                          // identity
    } else if mutation_kind == 1 && seed_total < 1000000 {
        seed_total + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_total > 1 {
        seed_total - 1                                      // nudge down
    } else if mutation_kind == 3 && seed_total <= 500000 {
        seed_total * 2                                      // double
    } else if mutation_kind == 4 {
        let h = seed_total / 2;
        if h < 1 { 1i32 } else { h }                       // halve
    } else if mutation_kind == 5 {
        1                                                   // min boundary
    } else if mutation_kind == 6 {
        1000000                                             // max boundary
    } else {
        seed_total                                          // fallback
    };

    let cost1 = if mutation_kind == 7 && seed_cost1 < 1000000 {
        seed_cost1 + 1                                      // nudge cost1 up
    } else if mutation_kind == 8 && seed_cost1 > 1 {
        seed_cost1 - 1                                      // nudge cost1 down
    } else if mutation_kind == 9 {
        1                                                   // min cost1
    } else if mutation_kind == 10 {
        1000000                                             // max cost1
    } else if mutation_kind == 11 {
        seed_total                                          // cost1 == total
    } else if mutation_kind == 12 && seed_total < 1000000 {
        seed_total + 1                                      // cost1 > total
    } else {
        seed_cost1                                          // identity
    };

    let cost2 = if mutation_kind == 13 && seed_cost2 < 1000000 {
        seed_cost2 + 1                                      // nudge cost2 up
    } else if mutation_kind == 14 && seed_cost2 > 1 {
        seed_cost2 - 1                                      // nudge cost2 down
    } else if mutation_kind == 15 {
        1                                                   // min cost2
    } else if mutation_kind == 16 {
        1000000                                             // max cost2
    } else if mutation_kind == 17 {
        seed_cost1                                          // cost2 == cost1
    } else if mutation_kind == 18 {
        seed_total                                          // cost2 == total
    } else {
        seed_cost2                                          // identity
    };

    (total, cost1, cost2)
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
    let num_mutations: u8 = 19;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (20, 10, 5),
        (5, 10, 10),
    ];
    for (t, c1, c2) in &examples {
        if count >= target_count { break; }
        if seen.insert((*t as i64, *c1 as i64, *c2 as i64)) {
            let result = Solution::ways_to_buy_pens_pencils(*t, *c1, *c2);
            writeln!(out, "{}", json!({
                "input": {"total": t, "cost1": c1, "cost2": c2},
                "output": result
            })).unwrap();
            count += 1;
        }
    }

    // Seed pool covering boundaries and interesting values
    let seed_vals: Vec<(i32, i32, i32)> = vec![
        (1, 1, 1),
        (1, 1, 1000000),
        (1, 1000000, 1),
        (1000000, 1, 1),
        (1000000, 1000000, 1000000),
        (1000000, 1, 1000000),
        (1000000, 1000000, 1),
        (1, 1000000, 1000000),
        (500000, 500000, 500000),
        (100, 10, 10),
        (100, 1, 100),
        (100, 100, 1),
        (999999, 1, 1),
        (2, 1, 1),
        (10, 3, 4),
        (1000000, 999999, 999999),
        (50, 7, 3),
        (1000, 100, 50),
    ];

    // Seed pool × mutation_kind
    for (st, sc1, sc2) in &seed_vals {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (total, cost1, cost2) = generate_test_case(*st, *sc1, *sc2, mk);
            if seen.insert((total as i64, cost1 as i64, cost2 as i64)) {
                let result = Solution::ways_to_buy_pens_pencils(total, cost1, cost2);
                writeln!(out, "{}", json!({
                    "input": {"total": total, "cost1": cost1, "cost2": cost2},
                    "output": result
                })).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let st = rng.gen_range_i64(1, 1000000) as i32;
        let sc1 = rng.gen_range_i64(1, 1000000) as i32;
        let sc2 = rng.gen_range_i64(1, 1000000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (total, cost1, cost2) = generate_test_case(st, sc1, sc2, mk);
        if seen.insert((total as i64, cost1 as i64, cost2 as i64)) {
            let result = Solution::ways_to_buy_pens_pencils(total, cost1, cost2);
            writeln!(out, "{}", json!({
                "input": {"total": total, "cost1": cost1, "cost2": cost2},
                "output": result
            })).unwrap();
            count += 1;
        }
    }
}
