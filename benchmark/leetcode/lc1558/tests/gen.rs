use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000000000,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 100000 { 100000usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 1000000000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        let value = if value < 0 { 0 } else if value > 1000000000 { 1000000000 } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(seed_nums: Vec<i32>, mutation_kind: u8) -> (nums: Vec<i32>)
    requires
        1 <= seed_nums.len() <= 100_000,
        forall|i: int| 0 <= i < seed_nums.len() ==> 0 <= #[trigger] seed_nums[i] <= 1_000_000_000,
    ensures
        1 <= nums@.len() <= 100_000,
        forall|i: int| 0 <= i < nums@.len() ==> 0 <= #[trigger] nums@[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        seed_nums
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut v = seed_nums;
        let last = v.len() - 1;
        v.set(last, 0);
        v
    } else if mutation_kind == 2 {
        // set last element to max boundary
        let mut v = seed_nums;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else if mutation_kind == 3 {
        // set all elements to a constant value
        let mut v = seed_nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == seed_nums.len(),
                1 <= v.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> v[j] == 500i32,
                forall|j: int| i <= j < v.len() ==> v[j] == seed_nums[j],
            decreases v.len() - i,
        {
            v.set(i, 500);
            i += 1;
        }
        v
    } else if mutation_kind == 4 && seed_nums.len() < 100_000 {
        // grow by one element
        let mut v = seed_nums;
        v.push(0);
        v
    } else if mutation_kind == 5 && seed_nums.len() > 1 {
        // shrink by one element
        let mut v = seed_nums;
        v.pop();
        v
    } else if mutation_kind == 6 {
        // nudge first element up
        let mut v = seed_nums;
        if v[0] < 1_000_000_000 {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 7 {
        // nudge first element down
        let mut v = seed_nums;
        if v[0] > 0 {
            v.set(0, v[0] - 1);
        }
        v
    } else if mutation_kind == 8 {
        // set first to 0 and last to max
        let mut v = seed_nums;
        v.set(0, 0);
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else if mutation_kind == 9 {
        // set all elements to 0
        let mut v = seed_nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == seed_nums.len(),
                1 <= v.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> v[j] == 0i32,
                forall|j: int| i <= j < v.len() ==> v[j] == seed_nums[j],
            decreases v.len() - i,
        {
            v.set(i, 0);
            i += 1;
        }
        v
    } else {
        // fallback: identity
        seed_nums
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

fn mutate(seed_nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_candidate(seed_nums, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 1_000_000_000) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1558);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let nums = generate_test_case(nums);
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_operations(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 5],
        vec![2, 2],
        vec![4, 2, 5],
    ];
    for nums in examples {
        emit(nums, &mut seen, &mut out, &mut count);
    }

    // Curated seed inputs
    let seed_inputs: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![1_000_000_000],
        vec![0, 0],
        vec![0, 0, 0],
        vec![1_000_000_000, 1_000_000_000, 1_000_000_000],
        vec![1, 2, 3, 4, 5],
        vec![7, 0, 3, 1_000_000_000],
        vec![0, 1],
        vec![1, 0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for seed_n in &seed_inputs {
        for &mk in &mutation_kinds {
            let result = mutate(seed_n.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random inputs across diverse size classes
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
