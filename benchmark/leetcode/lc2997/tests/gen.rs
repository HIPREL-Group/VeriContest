use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_vals: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= seed_vals.len() <= 100_000,
        0 <= k <= 1_000_000,
        forall|i: int| 0 <= i < seed_vals.len() ==> 0 <= #[trigger] seed_vals[i] <= 1_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 1_000_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000,
{
    if mutation_kind == 0 {
        // identity
        (seed_vals, k)
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut nums = seed_vals;
        let last = nums.len() - 1;
        nums.set(last, 0);
        (nums, k)
    } else if mutation_kind == 2 {
        // set last element to 1_000_000 (max boundary)
        let mut nums = seed_vals;
        let last = nums.len() - 1;
        nums.set(last, 1_000_000);
        (nums, k)
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut nums = seed_vals;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == seed_vals.len(),
                1 <= nums.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> nums[j] == 0,
                forall|j: int| i <= j < nums.len() ==> nums[j] == seed_vals[j],
            decreases nums.len() - i,
        {
            nums.set(i, 0);
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 4 && seed_vals.len() < 100_000 {
        // grow by one element (push 0)
        let mut nums = seed_vals;
        nums.push(0);
        (nums, k)
    } else if mutation_kind == 5 && seed_vals.len() > 1 {
        // shrink by one element (pop)
        let mut nums = seed_vals;
        nums.pop();
        (nums, k)
    } else if mutation_kind == 6 {
        // nudge last element up (if < 1_000_000)
        let mut nums = seed_vals;
        let last = nums.len() - 1;
        if nums[last] < 1_000_000 {
            nums.set(last, nums[last] + 1);
        }
        (nums, k)
    } else if mutation_kind == 7 {
        // nudge last element down (if > 0)
        let mut nums = seed_vals;
        let last = nums.len() - 1;
        if nums[last] > 0 {
            nums.set(last, nums[last] - 1);
        }
        (nums, k)
    } else if mutation_kind == 8 {
        // set k to 0
        (seed_vals, 0)
    } else if mutation_kind == 9 {
        // set k to max boundary
        (seed_vals, 1_000_000)
    } else if mutation_kind == 10 && seed_vals.len() >= 2 {
        // swap first two elements
        let mut nums = seed_vals;
        let tmp = nums[0];
        nums.set(0, nums[1]);
        nums.set(1, tmp);
        (nums, k)
    } else if mutation_kind == 11 {
        // set all elements to 1_000_000
        let mut nums = seed_vals;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == seed_vals.len(),
                1 <= nums.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> nums[j] == 1_000_000,
                forall|j: int| i <= j < nums.len() ==> nums[j] == seed_vals[j],
            decreases nums.len() - i,
        {
            nums.set(i, 1_000_000);
            i += 1;
        }
        (nums, k)
    } else {
        // fallback: identity
        (seed_vals, k)
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

fn mutate(seed_vals: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(seed_vals, k, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 1_000_000) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::collections::HashSet;
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}_{}", nums, k);
        if *count >= target || !seen.insert(key) {
            return;
        }
        let output = Solution::min_operations(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let example_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![2, 1, 3, 4], 1),
        (vec![2, 0, 2, 0], 0),
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    // Apply every mutation to example seeds
    for (seed_nums, k) in &example_seeds {
        for &mk in &mutation_kinds {
            let (nums, k_out) = mutate(seed_nums.clone(), *k, mk);
            emit(nums, k_out, &mut seen, &mut out, &mut count);
        }
    }

    // Hand-crafted boundary seeds
    let boundary_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![0], 0),
        (vec![1_000_000], 1_000_000),
        (vec![0, 0, 0], 0),
        (vec![1_000_000, 1_000_000], 1_000_000),
        (vec![0], 1_000_000),
        (vec![1_000_000], 0),
    ];

    for (seed_nums, k) in &boundary_seeds {
        for &mk in &mutation_kinds {
            let (nums, k_out) = mutate(seed_nums.clone(), *k, mk);
            emit(nums, k_out, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 10000),   // very large
        };
        let nums = random_nums(&mut rng, n);
        let k = rng.gen_range_i64(0, 1_000_000) as i32;
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (nums_out, k_out) = mutate(nums, k, mk);
        emit(nums_out, k_out, &mut seen, &mut out, &mut count);
    }
}
