use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        nums.len() >= 1,
        nums.len() <= 100_000,
    ensures
        result.len() >= 1,
        result.len() <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut v = nums;
        v.set(0, 0);
        v
    } else if mutation_kind == 2 {
        // set first element to -1
        let mut v = nums;
        v.set(0, -1);
        v
    } else if mutation_kind == 3 {
        // set first element to 1
        let mut v = nums;
        v.set(0, 1);
        v
    } else if mutation_kind == 4 {
        // set all elements to 1
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100_000,
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 5 {
        // set all elements to -1 (all negative, answer should be 1)
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100_000,
            decreases v.len() - i,
        {
            v.set(i, -1);
            i += 1;
        }
        v
    } else if mutation_kind == 6 && nums.len() < 100_000 {
        // grow by one element
        let mut v = nums;
        v.push(0);
        v
    } else if mutation_kind == 7 && nums.len() > 1 {
        // shrink by one element
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 8 && nums.len() >= 2 {
        // swap first two elements
        let mut v = nums;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        v
    } else if mutation_kind == 9 {
        // set last element to i32::MAX
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, i32::MAX);
        v
    } else if mutation_kind == 10 {
        // set last element to i32::MIN
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, i32::MIN);
        v
    } else {
        // fallback
        nums
    }
}

} // verus!

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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize, val_lo: i64, val_hi: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(val_lo, val_hi) as i32);
    }
    v
}

// Build [1, 2, ..., n] — answer should be n+1
fn consecutive_from_one(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 1..=n {
        v.push(i as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(41);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::first_missing_positive(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 0],
        vec![3, 4, -1, 1],
        vec![7, 8, 9, 11, 12],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Structured seeds
    let structured_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![2],
        vec![0],
        vec![-1],
        vec![i32::MAX],
        vec![i32::MIN],
        consecutive_from_one(1),
        consecutive_from_one(5),
        consecutive_from_one(10),
        vec![2, 1],
        vec![-1, -2, -3],
        vec![0, 0, 0],
        vec![1, 1, 1],
        vec![2, 3, 4],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply every mutation to every structured seed
    for seed_arr in &structured_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse size classes and value ranges, with mutations
    for i in 0..200 {
        if count >= target_count { break; }
        // Size classes
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 10000),   // big
        };
        // Value range diversity
        let (val_lo, val_hi): (i64, i64) = match i % 4 {
            0 => (-10, 10),                          // small range
            1 => (1, n as i64 + 5),                  // positive, near n
            2 => (-1_000_000, 1_000_000),            // medium range
            _ => (i32::MIN as i64, i32::MAX as i64), // full range
        };
        let seed_arr = random_nums(&mut rng, n, val_lo, val_hi);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(seed_arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity-mutated random arrays
    while count < target_count {
        let n = rng.gen_range_usize(1, 100_000.min(5000));
        let seed_arr = random_nums(&mut rng, n, -100, (n as i64) + 10);
        emit(mutate(seed_arr, 0), &mut seen, &mut out, &mut count);
    }
}
