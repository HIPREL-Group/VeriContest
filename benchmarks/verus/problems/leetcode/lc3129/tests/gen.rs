use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_zero: i32,
    seed_one: i32,
    seed_limit: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32))
    requires
        1 <= seed_zero <= 200,
        1 <= seed_one <= 200,
        1 <= seed_limit <= 200,
    ensures
        1 <= result.0 <= 200,
        1 <= result.1 <= 200,
        1 <= result.2 <= 200,
{
    if mutation_kind == 0 {
        (seed_zero, seed_one, seed_limit)
    } else if mutation_kind == 1 && seed_zero < 200 {
        (seed_zero + 1, seed_one, seed_limit)
    } else if mutation_kind == 2 && seed_zero > 1 {
        (seed_zero - 1, seed_one, seed_limit)
    } else if mutation_kind == 3 && seed_one < 200 {
        (seed_zero, seed_one + 1, seed_limit)
    } else if mutation_kind == 4 && seed_one > 1 {
        (seed_zero, seed_one - 1, seed_limit)
    } else if mutation_kind == 5 && seed_limit < 200 {
        (seed_zero, seed_one, seed_limit + 1)
    } else if mutation_kind == 6 && seed_limit > 1 {
        (seed_zero, seed_one, seed_limit - 1)
    } else if mutation_kind == 7 {
        (1, seed_one, seed_limit)
    } else if mutation_kind == 8 {
        (200, seed_one, seed_limit)
    } else if mutation_kind == 9 {
        (seed_zero, 1, seed_limit)
    } else if mutation_kind == 10 {
        (seed_zero, 200, seed_limit)
    } else if mutation_kind == 11 {
        (seed_zero, seed_one, 1)
    } else if mutation_kind == 12 {
        (seed_zero, seed_one, 200)
    } else if mutation_kind == 13 {
        (1, 1, 1)
    } else if mutation_kind == 14 {
        (200, 200, 200)
    } else if mutation_kind == 15 {
        let hz = seed_zero / 2;
        if hz >= 1 { (hz, seed_one, seed_limit) } else { (1, seed_one, seed_limit) }
    } else if mutation_kind == 16 {
        let ho = seed_one / 2;
        if ho >= 1 { (seed_zero, ho, seed_limit) } else { (seed_zero, 1, seed_limit) }
    } else if mutation_kind == 17 {
        let hl = seed_limit / 2;
        if hl >= 1 { (seed_zero, seed_one, hl) } else { (seed_zero, seed_one, 1) }
    } else if mutation_kind == 18 {
        let dz = if seed_zero <= 100 { seed_zero * 2 } else { 200 };
        (dz, seed_one, seed_limit)
    } else if mutation_kind == 19 {
        let d_one = if seed_one <= 100 { seed_one * 2 } else { 200 };
        (seed_zero, d_one, seed_limit)
    } else if mutation_kind == 20 {
        let dl = if seed_limit <= 100 { seed_limit * 2 } else { 200 };
        (seed_zero, seed_one, dl)
    } else if mutation_kind == 21 {
        (seed_one, seed_zero, seed_limit)
    } else if mutation_kind == 22 {
        (seed_zero, seed_one, seed_zero)
    } else if mutation_kind == 23 {
        (seed_zero, seed_one, seed_one)
    } else {
        (seed_zero, seed_one, seed_limit)
    }
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

// Keep values small so the naive-recursive code.rs finishes quickly.
const MAX_SEED: i64 = 12;
const NUM_MUTATIONS: u8 = 24;

struct Solution;
include!("../code.rs");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    use std::io::Write;

    let seed_pool: Vec<(i32, i32, i32)> = vec![
        (1, 1, 2),
        (1, 2, 1),
        (3, 3, 2),
        (1, 1, 1),
        (MAX_SEED as i32, MAX_SEED as i32, MAX_SEED as i32),
        (1, MAX_SEED as i32, 1),
        (MAX_SEED as i32, 1, 1),
        (1, 1, MAX_SEED as i32),
        (MAX_SEED as i32, MAX_SEED as i32, 1),
        (6, 6, 6),
        (2, 2, 1),
        (3, 2, 2),
        (5, 5, 3),
        (1, 5, 1),
        (5, 1, 1),
        (10, 10, 5),
        (8, 7, 4),
        (4, 4, 3),
    ];

    let mut case_idx: usize = 0;

    // Phase 1: Curated seeds × all mutations
    for &(sz, so, sl) in &seed_pool {
        for mk in 0..NUM_MUTATIONS {
            if case_idx >= count { break; }
            let (zero, one, limit) = generate_test_case(sz, so, sl, mk);
            // Clamp for runtime performance (recursive code.rs is slow on large inputs)
            let zero = if zero > MAX_SEED as i32 { MAX_SEED as i32 } else { zero };
            let one = if one > MAX_SEED as i32 { MAX_SEED as i32 } else { one };
            let limit = if limit > MAX_SEED as i32 { MAX_SEED as i32 } else { limit };
            let result = Solution::number_of_stable_arrays(zero, one, limit);
            writeln!(out, "{}", json!({
                "input": {"zero": zero, "one": one, "limit": limit},
                "output": result
            })).unwrap();
            case_idx += 1;
        }
        if case_idx >= count { break; }
    }

    // Phase 2: Random seeds × random mutations
    let mut _attempts = 0usize;
    while case_idx < count {
        _attempts += 1;
        if _attempts > 10000 { break; }

        let sz = match case_idx % 4 {
            0 => rng.gen_range_i64(1, 3) as i32,
            1 => rng.gen_range_i64(1, 6) as i32,
            2 => rng.gen_range_i64(4, 9) as i32,
            _ => rng.gen_range_i64(7, MAX_SEED) as i32,
        };
        let so = match (case_idx / 4) % 4 {
            0 => rng.gen_range_i64(1, 3) as i32,
            1 => rng.gen_range_i64(1, 6) as i32,
            2 => rng.gen_range_i64(4, 9) as i32,
            _ => rng.gen_range_i64(7, MAX_SEED) as i32,
        };
        let sl = match (case_idx / 16) % 4 {
            0 => rng.gen_range_i64(1, 3) as i32,
            1 => rng.gen_range_i64(1, 6) as i32,
            2 => rng.gen_range_i64(4, 9) as i32,
            _ => rng.gen_range_i64(7, MAX_SEED) as i32,
        };

        let mk = rng.gen_u8() % NUM_MUTATIONS;

        let (zero, one, limit) = generate_test_case(sz, so, sl, mk);
        // Clamp for runtime performance
        let zero = if zero > MAX_SEED as i32 { MAX_SEED as i32 } else { zero };
        let one = if one > MAX_SEED as i32 { MAX_SEED as i32 } else { one };
        let limit = if limit > MAX_SEED as i32 { MAX_SEED as i32 } else { limit };
        let result = Solution::number_of_stable_arrays(zero, one, limit);
        writeln!(out, "{}", json!({
            "input": {"zero": zero, "one": one, "limit": limit},
            "output": result
        })).unwrap();
        case_idx += 1;
    }

    eprintln!("Generated {} test cases to {}", case_idx, out_path.display());
}
