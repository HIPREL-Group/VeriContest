use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_start: i32, seed_goal: i32, mutation_kind: u8) -> (res: (i32, i32))
    ensures
        0 <= res.0 <= 1000000000,
        0 <= res.1 <= 1000000000,
{
    let seed_start = if seed_start < 0 { 0 } else if seed_start > 1000000000 { 1000000000 } else { seed_start };
    let seed_goal = if seed_goal < 0 { 0 } else if seed_goal > 1000000000 { 1000000000 } else { seed_goal };
    let start = if mutation_kind == 0 {
        seed_start                                          // identity
    } else if mutation_kind == 1 && seed_start < i32::MAX {
        seed_start + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_start > 0 {
        seed_start - 1                                      // nudge down
    } else if mutation_kind == 3 && seed_start >= 0 && seed_start <= 1_073_741_823 {
        seed_start * 2                                      // double
    } else if mutation_kind == 4 {
        seed_start / 2                                      // halve
    } else if mutation_kind == 5 {
        0                                                   // zero
    } else if mutation_kind == 6 {
        i32::MAX                                            // max boundary
    } else {
        seed_start
    };

    let goal = if mutation_kind == 7 && seed_goal < i32::MAX {
        seed_goal + 1                                       // nudge up
    } else if mutation_kind == 8 && seed_goal > 0 {
        seed_goal - 1                                       // nudge down
    } else if mutation_kind == 9 {
        seed_start                                          // same as start seed
    } else if mutation_kind == 10 {
        if seed_goal <= i32::MAX - seed_start {
            seed_start + seed_goal                          // combine
        } else {
            seed_goal
        }
    } else {
        seed_goal
    };

    (if start > 1000000000 { 1000000000 } else { start },
     if goal > 1000000000 { 1000000000 } else { goal })
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0;
    let num_mutations: u8 = 11;

    // Example inputs from the problem description
    let examples: Vec<(i32, i32)> = vec![
        (10, 7),
        (3, 4),
    ];
    for (s, g) in &examples {
        if generated >= count { break; }
        if seen.insert((*s as i64, *g as i64)) {
            let result = Solution::min_bit_flips(*s, *g);
            writeln!(out, "{}", json!({"input": {"start": s, "goal": g}, "output": result})).unwrap();
            generated += 1;
        }
    }

    // Seed pool with boundary and interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (0, 0), (0, i32::MAX), (i32::MAX, 0), (i32::MAX, i32::MAX),
        (1, 0), (0, 1), (1, 1), (1, 2), (1, 4),
        (2, 4), (4, 8), (8, 16), (16, 32),
        (1024, 2048), (1 << 15, 1 << 16), (1 << 20, 1 << 21), (1 << 29, 1 << 30),
        (42, 42), (255, 256), (1023, 1024), (100, 101),
        (0x7FFF_FFFF, 0), (0x5555_5555, 0x2AAA_AAAA),
        (0x7F7F_7F7F, 0x0F0F_0F0F),
    ];

    // Seed pool × mutation_kind
    for &(ss, sg) in &seeds {
        for mk in 0..num_mutations {
            if generated >= count { break; }
            let (start, goal) = generate_test_case(ss, sg, mk);
            if seen.insert((start as i64, goal as i64)) {
                let result = Solution::min_bit_flips(start, goal);
                writeln!(out, "{}", json!({"input": {"start": start, "goal": goal}, "output": result})).unwrap();
                generated += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while generated < count {
        let ss = rng.gen_range_i64(0, i32::MAX as i64) as i32;
        let sg = rng.gen_range_i64(0, i32::MAX as i64) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (start, goal) = generate_test_case(ss, sg, mk);
        if seen.insert((start as i64, goal as i64)) {
            let result = Solution::min_bit_flips(start, goal);
            writeln!(out, "{}", json!({"input": {"start": start, "goal": goal}, "output": result})).unwrap();
            generated += 1;
        }
    }
}
