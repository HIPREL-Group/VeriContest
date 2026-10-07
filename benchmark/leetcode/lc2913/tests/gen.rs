use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 2 {
        // set last element to 100 (max boundary)
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 100);
        v
    } else if mutation_kind == 3 {
        // set all elements to 1 (all same, min)
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100,
                forall|j: int| 0 <= j < i ==> v[j] == 1i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 4 {
        // set all elements to 100 (all same, max)
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100,
                forall|j: int| 0 <= j < i ==> v[j] == 100i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 100);
            i += 1;
        }
        v
    } else if mutation_kind == 5 && nums.len() < 100 {
        // grow by one element
        let mut v = nums;
        v.push(1);
        v
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink by one element
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 7 {
        // nudge last element up (if < 100, increment by 1)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] < 100 {
            v.set(last, v[last] + 1);
        }
        v
    } else if mutation_kind == 8 {
        // nudge last element down (if > 1, decrement by 1)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] > 1 {
            v.set(last, v[last] - 1);
        }
        v
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first and last elements
        let mut v = nums;
        let last = v.len() - 1;
        let first_val = v[0];
        let last_val = v[last];
        v.set(0, last_val);
        if last != 0 {
            v.set(last, first_val);
        }
        v
    } else {
        // fallback: identity
        nums
    }
}

} // verus!

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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2913);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::sum_counts(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 1],
        vec![1, 1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to example inputs
    for seed_nums in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(seed_nums.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Curated seeds for diversity
    let curated_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100],
        vec![1, 100],
        vec![50, 50, 50],
        vec![1, 2, 3, 4, 5],
        vec![100, 99, 98, 97, 96],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ];

    for seed_nums in &curated_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_nums.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Size classes with random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),    // tiny
        (4, 10),   // small
        (11, 30),  // medium
        (31, 60),  // large
        (61, 100), // max
    ];

    for &(lo, hi) in &size_classes {
        for _ in 0..5 {
            let len = rng.gen_range_usize(lo, hi);
            let seed_nums = random_nums(&mut rng, len);
            let mk = rng.gen_range_usize(0, 9) as u8;
            let result = mutate(seed_nums, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random seeds and mutations
    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let seed_nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
