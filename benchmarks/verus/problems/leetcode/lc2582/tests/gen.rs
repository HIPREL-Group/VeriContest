use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_time: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        2 <= seed_n <= 1000,
        1 <= seed_time <= 1000,
    ensures
        2 <= res.0 <= 1000,
        1 <= res.1 <= 1000,
{
    let n = if mutation_kind == 0 {
        seed_n
    } else if mutation_kind == 1 && seed_n < 1000 {
        seed_n + 1
    } else if mutation_kind == 2 && seed_n > 2 {
        seed_n - 1
    } else if mutation_kind == 3 && seed_n >= 4 {
        seed_n / 2
    } else if mutation_kind == 4 {
        2
    } else if mutation_kind == 5 {
        1000
    } else if mutation_kind == 6 {
        500
    } else {
        seed_n
    };

    let time = if mutation_kind == 7 && seed_time < 1000 {
        seed_time + 1
    } else if mutation_kind == 8 && seed_time > 1 {
        seed_time - 1
    } else if mutation_kind == 9 {
        1
    } else if mutation_kind == 10 {
        1000
    } else if mutation_kind == 11 && seed_time >= 2 {
        seed_time / 2
    } else if mutation_kind == 12 && seed_time <= 500 {
        seed_time * 2
    } else if mutation_kind == 13 {
        seed_n - 1
    } else if mutation_kind == 14 && seed_n <= 501 {
        // time = 2*(n-1), a full cycle
        (seed_n - 1) * 2
    } else {
        seed_time
    };

    (n, time)
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
    let mut count = 0;
    let num_mutations: u8 = 15;

    // Example inputs from description + boundary seeds
    let seeds: Vec<(i32, i32)> = vec![
        (4, 5), (3, 2),                          // examples from description
        (2, 1), (2, 2), (2, 1000),                // min n
        (1000, 1), (1000, 1000), (1000, 999),     // max n
        (2, 1000), (500, 500),                    // mid-range
        (3, 1), (3, 3), (3, 4), (3, 5), (3, 6),  // small n, various times
        (10, 1), (10, 9), (10, 10), (10, 18),     // n=10 boundaries
        (100, 99), (100, 100), (100, 198),         // n=100 cycle
        (4, 1), (4, 3), (4, 6), (4, 7),           // n=4 cycle points
    ];

    // Seed pool × mutation_kind
    for &(sn, st) in &seeds {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (n, time) = generate_test_case(sn, st, mk);
            if seen.insert((n, time)) {
                let result = Solution::pass_the_pillow(n, time);
                writeln!(out, "{}", json!({"input": {"n": n, "time": time}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let sn = rng.gen_range_i64(2, 1000) as i32;
        let st = rng.gen_range_i64(1, 1000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, time) = generate_test_case(sn, st, mk);
        if seen.insert((n, time)) {
            let result = Solution::pass_the_pillow(n, time);
            writeln!(out, "{}", json!({"input": {"n": n, "time": time}, "output": result})).unwrap();
            count += 1;
        }
    }
}
