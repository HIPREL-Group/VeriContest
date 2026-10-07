use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 40000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
    ensures
        1 <= result.len() <= 40000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (min value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        // set last element to 10000 (max value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 10000);
        d
    } else if mutation_kind == 3 && nums.len() < 40000 {
        // grow by one element (push 1)
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 4 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 5 {
        // set all elements to 3 (divisible by 3)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 40000,
                forall|j: int| 0 <= j < i ==> d[j] == 3,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 3);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // nudge last element up: if < 10000, increment by 1
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 10000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge last element down: if > 1, decrement by 1
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 8 {
        // set first element to 10000
        let mut d = nums;
        d.set(0, 10000);
        d
    } else if mutation_kind == 9 {
        // set all elements to 1 (remainder 1 mod 3)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 40000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 10 {
        // set all elements to 2 (remainder 2 mod 3)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 40000,
                forall|j: int| 0 <= j < i ==> d[j] == 2,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 2);
            i += 1;
        }
        d
    } else {
        nums // fallback
    }
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
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 10000) as i32);
    }
    nums
}

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1262);
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
        let output = Solution::max_sum_div_three(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![3, 6, 5, 1, 8],      // example 1 => 18
        vec![4],                    // example 2 => 0
        vec![1, 2, 3, 4, 4],      // example 3 => 12
    ];

    // Interesting hand-crafted seeds
    let hand_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![3],
        vec![10000],
        vec![1, 1],
        vec![2, 2],
        vec![3, 3],
        vec![1, 2, 3],
        vec![9999, 9999, 9999],
        vec![1, 1, 1],
        vec![2, 1],
        vec![7, 7, 7],
        vec![5, 5, 5, 5],
        vec![10000, 10000, 10000],
    ];

    let mutation_kinds: Vec<u8> = (0..=10).collect();

    // Apply mutations to example seeds
    for seed_vec in &example_seeds {
        for &mk in &mutation_kinds {
            if count >= target_count { break; }
            let result = mutate(seed_vec.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Apply mutations to hand-crafted seeds
    for seed_vec in &hand_seeds {
        for &mk in &mutation_kinds {
            if count >= target_count { break; }
            let result = mutate(seed_vec.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse sizes and random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),        // tiny
        (6, 20),       // small
        (21, 100),     // medium
        (101, 1000),   // large
        (1001, 5000),  // xl
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            if count >= target_count { break; }
            let len = rng.gen_range_usize(*lo, *hi);
            let seed_vec = random_nums(&mut rng, len);
            let mk = rng.gen_range_usize(0, 10) as u8;
            let result = mutate(seed_vec, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random seeds, identity mutation
    while count < target_count {
        let len = rng.gen_range_usize(1, 5000);
        let seed_vec = random_nums(&mut rng, len);
        emit(mutate(seed_vec, 0), &mut seen, &mut out, &mut count);
    }
}
