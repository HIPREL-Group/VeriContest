use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 5000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 5000,
    ensures
        1 <= result.len() <= 5000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 5000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 0 (even boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 1 (odd boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 3 {
        // set all elements to an even value (2)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 5000,
                forall|j: int| 0 <= j < i ==> d[j] == 2,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 2);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to an odd value (1)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 5000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && nums.len() < 5000 {
        // grow by one element (push 0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // set last element to 5000 (max boundary, even)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 5000);
        d
    } else if mutation_kind == 8 {
        // set last element to 4999 (near-max, odd)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 4999);
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let tmp0 = d[0];
        let tmp1 = d[last];
        d.set(0, tmp1);
        d.set(last, tmp0);
        d
    } else if mutation_kind == 10 {
        // nudge last element up by 1 if < 5000
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 5000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 11 {
        // nudge last element down by 1 if > 0
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 0 {
            d.set(last, d[last] - 1);
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
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 5000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
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
        let output = Solution::sort_array_by_parity(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![3, 1, 2, 4],
        vec![0],
    ];

    // Interesting seed arrays
    let extra_seeds: Vec<Vec<i32>> = vec![
        vec![2, 4, 6, 8],           // all even
        vec![1, 3, 5, 7],           // all odd
        vec![0, 0, 0],              // all zeros
        vec![5000],                 // single max
        vec![1],                    // single odd
        vec![2],                    // single even
        vec![1, 2],                 // one odd, one even
        vec![2, 1],                 // one even, one odd
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], // alternating parity
        vec![4999, 5000],           // boundary values
        vec![0, 1],                 // min values
        vec![0, 5000, 1, 4999, 2],  // mixed boundaries
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    // Apply mutations to example seeds
    for seed in &example_seeds {
        for &mk in &mutation_kinds {
            emit(mutate(seed.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Apply mutations to extra seeds
    for seed in &extra_seeds {
        for &mk in &mutation_kinds {
            emit(mutate(seed.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    for i in 0..200 {
        if count >= target { break; }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // max
        };
        let seed = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 11) as u8;
        emit(mutate(seed, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity mutations
    while count < target {
        let n = rng.gen_range_usize(1, 5000);
        let seed = random_nums(&mut rng, n);
        emit(mutate(seed, 0), &mut seen, &mut out, &mut count);
    }
}
