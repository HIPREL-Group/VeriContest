use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_start: i32, mutation_kind: u8) -> (result: (i32, i32))
    requires
        1 <= seed_n <= 16,
        0 <= seed_start < (1i32 << (seed_n as u32)),
    ensures
        1 <= result.0 <= 16,
        0 <= result.1 < (1i32 << (result.0 as u32)),
{
    let bound: i32 = 1i32 << (seed_n as u32);

    let start: i32 = if mutation_kind == 1 {
        0i32
    } else if mutation_kind == 2 {
        bound - 1
    } else if mutation_kind == 3 && seed_start > 0 {
        seed_start - 1
    } else if mutation_kind == 4 && seed_start < bound - 1 {
        seed_start + 1
    } else if mutation_kind == 5 {
        seed_start / 2
    } else {
        seed_start
    };

    (seed_n, start)
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
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
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(30);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (2, 3),
        (3, 2),
    ];
    for (n, start) in &examples {
        if seen.insert((*n, *start)) {
            let result = Solution::circular_permutation(*n, *start);
            writeln!(out, "{}", json!({"input": {"n": n, "start": start}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: interesting (n, seed_start) pairs — seed_start must be in [0, 2^n)
    // Keep n <= 4 since code.rs runs in O(2^n) time
    let seed_pool: Vec<(i32, i32)> = vec![
        (1, 0), (1, 1),
        (2, 0), (2, 1), (2, 2), (2, 3),
        (3, 0), (3, 4), (3, 7),
        (4, 0), (4, 8), (4, 15),
    ];
    let num_mutations: u8 = 6;

    for &(sn, ss) in &seed_pool {
        for mk in 0..num_mutations {
            if count >= count_goal { break; }
            let (n, start) = generate_test_case(sn, ss, mk);
            if seen.insert((n, start)) {
                let result = Solution::circular_permutation(n, start);
                writeln!(out, "{}", json!({"input": {"n": n, "start": start}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    let mut attempts = 0usize;
    while count < count_goal && attempts < count_goal * 20 {
        attempts += 1;
        // Vary n across size classes
        let sn = match count % 5 {
            0 => rng.gen_range_i64(1, 2) as i32,    // tiny
            1 => rng.gen_range_i64(1, 3) as i32,    // small
            2 => rng.gen_range_i64(2, 4) as i32,    // medium
            3 => rng.gen_range_i64(3, 4) as i32,    // large
            _ => 4i32,                               // max
        };
        let max_start = (1i64 << (sn as u32)) - 1;
        let ss = rng.gen_range_i64(0, max_start) as i32;
        let mk = rng.gen_u8() % num_mutations;
        let (n, start) = generate_test_case(sn, ss, mk);
        if seen.insert((n, start)) {
            let result = Solution::circular_permutation(n, start);
            writeln!(out, "{}", json!({"input": {"n": n, "start": start}, "output": result})).unwrap();
            count += 1;
        }
    }
}
