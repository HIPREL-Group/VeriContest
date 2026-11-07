use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 100,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        // set last element to 100 (maximum value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to 100
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 100i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 100);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && nums.len() < 100 {
        // grow: push element 50
        let mut d = nums;
        d.push(50);
        d
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // nudge first element up: if < 100, increment by 1
        let mut d = nums;
        if d[0] < 100 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge first element down: if > 1, decrement by 1
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 9 {
        // set first element to 100, rest to 1 (maximally dominant first)
        let mut d = nums;
        d.set(0, 100);
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                d[0] == 100i32,
                forall|j: int| 1 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
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
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3833);
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
        let output = Solution::dominant_indices(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![5, 4, 3],
        vec![4, 1, 2],
    ];

    // Hand-crafted seeds for diversity
    let crafted_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100],
        vec![50, 50],
        vec![100, 1],
        vec![1, 100],
        vec![1, 1, 1],
        vec![100, 100, 100],
        vec![100, 1, 1, 1, 1],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![50, 25, 75],
        vec![1, 100, 1, 100],
        vec![99, 1],
        vec![2, 1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Emit examples first (identity mutation)
    for seed_vec in &example_seeds {
        emit(seed_vec.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every crafted seed
    for seed_vec in &crafted_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_vec.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse sizes and random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),     // tiny
        (4, 10),    // small
        (11, 30),   // medium
        (31, 70),   // large
        (71, 100),  // max
    ];

    for i in 0..60 {
        let (lo, hi) = size_classes[i % size_classes.len()];
        let len = rng.gen_range_usize(lo, hi);
        let seed_vec = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_vec, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(4, 10),
            2 => rng.gen_range_usize(11, 30),
            3 => rng.gen_range_usize(31, 70),
            _ => rng.gen_range_usize(71, 100),
        };
        let seed_vec = random_nums(&mut rng, len);
        emit(mutate(seed_vec, 0), &mut seen, &mut out, &mut count);
    }
}
