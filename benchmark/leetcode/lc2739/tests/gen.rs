use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_main: i32,
    seed_additional: i32,
    mutation_kind: u8,
) -> (res: (i32, i32))
    ensures
        1 <= res.0 <= 100,
        1 <= res.1 <= 100,
{
    let seed_main = if seed_main < 1 { 1 } else if seed_main > 100 { 100 } else { seed_main };
    let seed_additional = if seed_additional < 1 { 1 } else if seed_additional > 100 { 100 } else { seed_additional };
    let main_tank = if mutation_kind == 0 {
        seed_main                                         // identity
    } else if mutation_kind == 1 && seed_main < 100 {
        seed_main + 1                                     // nudge up
    } else if mutation_kind == 2 && seed_main > 1 {
        seed_main - 1                                     // nudge down
    } else if mutation_kind == 3 && seed_main <= 50 {
        seed_main * 2                                     // double
    } else if mutation_kind == 4 {
        seed_main / 2                                     // halve
    } else if mutation_kind == 5 {
        1                                                 // min boundary
    } else if mutation_kind == 6 {
        100                                               // max boundary
    } else if mutation_kind == 7 {
        5                                                 // transfer threshold
    } else if mutation_kind == 8 {
        4                                                 // just below threshold
    } else {
        seed_main                                         // fallback
    };

    let additional_tank = if mutation_kind == 9 && seed_additional < 100 {
        seed_additional + 1                               // nudge up
    } else if mutation_kind == 10 && seed_additional > 1 {
        seed_additional - 1                               // nudge down
    } else if mutation_kind == 11 {
        0                                                 // zero (no transfer)
    } else if mutation_kind == 12 {
        100                                               // max boundary
    } else if mutation_kind == 13 {
        1                                                 // min boundary
    } else if mutation_kind == 14 && seed_additional <= 50 {
        seed_additional * 2                               // double
    } else if mutation_kind == 15 {
        seed_additional / 2                               // halve
    } else {
        seed_additional                                   // fallback
    };

    (if main_tank < 1 { 1 } else { main_tank },
     if additional_tank < 1 { 1 } else { additional_tank })
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 16;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![(5, 10), (1, 2)];
    for &(mt, at) in &examples {
        if count >= goal { break; }
        if seen.insert((mt, at)) {
            let output = Solution::distance_traveled(mt, at);
            writeln!(out, "{}", json!({"input": {"mainTank": mt, "additionalTank": at}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary and interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 100), (100, 1), (100, 100),
        (1, 0), (5, 0), (5, 1), (4, 1), (4, 100),
        (10, 10), (50, 50), (99, 99), (100, 0),
        (5, 5), (9, 1), (10, 2), (20, 4),
        (6, 1), (8, 2), (12, 3), (50, 10),
        (1, 50), (2, 50), (3, 100), (100, 50),
    ];

    // Seed pool × mutation_kind
    for &(sm, sa) in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (mt, at) = generate_test_case(sm, sa, mk);
            if seen.insert((mt, at)) {
                let output = Solution::distance_traveled(mt, at);
                writeln!(out, "{}", json!({"input": {"mainTank": mt, "additionalTank": at}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let sm = rng.gen_range_i64(1, 100) as i32;
        let sa = rng.gen_range_i64(1, 100) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (mt, at) = generate_test_case(sm, sa, mk);
        if seen.insert((mt, at)) {
            let output = Solution::distance_traveled(mt, at);
            writeln!(out, "{}", json!({"input": {"mainTank": mt, "additionalTank": at}, "output": output})).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
