use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_arrival: i32, seed_delayed: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_arrival < 24,
        1 <= seed_delayed <= 24,
    ensures
        1 <= res.0 < 24,
        1 <= res.1 <= 24,
{
    let arrival = if mutation_kind == 0 {
        seed_arrival                                           // identity
    } else if mutation_kind == 1 && seed_arrival < 23 {
        seed_arrival + 1                                       // nudge up
    } else if mutation_kind == 2 && seed_arrival > 1 {
        seed_arrival - 1                                       // nudge down
    } else if mutation_kind == 3 {
        1                                                      // min boundary
    } else if mutation_kind == 4 {
        23                                                     // max boundary
    } else if mutation_kind == 5 {
        12                                                     // midpoint
    } else if mutation_kind == 6 && seed_arrival >= 1 && seed_arrival < 24 {
        if seed_arrival <= 12 { seed_arrival } else { 24 - seed_arrival }  // fold to lower half
    } else {
        seed_arrival                                           // fallback
    };

    let delayed = if mutation_kind == 7 && seed_delayed < 24 {
        seed_delayed + 1                                       // nudge up
    } else if mutation_kind == 8 && seed_delayed > 1 {
        seed_delayed - 1                                       // nudge down
    } else if mutation_kind == 9 {
        1                                                      // min boundary
    } else if mutation_kind == 10 {
        24                                                     // max boundary
    } else if mutation_kind == 11 {
        12                                                     // midpoint
    } else if mutation_kind == 12 {
        seed_delayed                                           // identity (mutate arrival only)
    } else {
        seed_delayed                                           // fallback
    };

    (arrival, delayed)
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 13;

    // Example inputs from description
    let examples: Vec<(i32, i32)> = vec![(15, 5), (13, 11)];
    for (a, d) in &examples {
        if count >= goal { break; }
        if seen.insert((*a, *d)) {
            let output = Solution::find_delayed_arrival_time(*a, *d);
            writeln!(out, "{}", json!({"input": {"arrivalTime": a, "delayedTime": d}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary and interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 24), (23, 1), (23, 24),
        (1, 12), (12, 1), (12, 12), (12, 24),
        (23, 12), (6, 6), (18, 18), (10, 14),
        (1, 23), (22, 2), (11, 13), (20, 4),
    ];

    for &(sa, sd) in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (arrival, delayed) = generate_test_case(sa, sd, mk);
            if seen.insert((arrival, delayed)) {
                let output = Solution::find_delayed_arrival_time(arrival, delayed);
                writeln!(out, "{}", json!({"input": {"arrivalTime": arrival, "delayedTime": delayed}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let sa = rng.gen_range_i64(1, 23) as i32;
        let sd = rng.gen_range_i64(1, 24) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (arrival, delayed) = generate_test_case(sa, sd, mk);
        if seen.insert((arrival, delayed)) {
            let output = Solution::find_delayed_arrival_time(arrival, delayed);
            writeln!(out, "{}", json!({"input": {"arrivalTime": arrival, "delayedTime": delayed}, "output": output})).unwrap();
            count += 1;
        }
    }
}
