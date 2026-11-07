use vstd::prelude::*;

verus! {

pub open spec fn is_prime(n: int) -> bool {
    n >= 2 && forall|d: int| 2 <= d < n ==> #[trigger] (n % d) != 0
}

pub fn prime_input(n: i32) -> (result: bool)
    requires 2 <= n <= 1000,
    ensures result == is_prime(n as int),
{
    let mut d = 2i32;
    while d < n
        invariant
            2 <= d <= n <= 1000,
            forall|k: int| 2 <= k < d ==> #[trigger] (n as int % k) != 0,
        decreases n - d,
    {
        if n % d == 0 { return false; }
        d += 1;
    }
    true
}

pub fn generate_test_case(raw: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 2 <= #[trigger] result[i] <= 1000,
        forall|i: int| 0 <= i < result.len() ==> is_prime(#[trigger] result[i] as int),
{
    let n = if raw.len() < 1 { 1usize } else if raw.len() > 100 { 100usize } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 2 <= #[trigger] result[j] <= 1000,
            forall|j: int| 0 <= j < result.len() ==> is_prime(#[trigger] result[j] as int),
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 2 };
        let v = if v < 2 { 2 } else if v > 1000 { 1000 } else { v };
        let v = if prime_input(v) { v } else { 2 };
        result.push(v);
        i += 1;
    }
    result
}


pub fn generate_candidate(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= 2,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] <= 1000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] >= 2,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to min boundary (2)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 2);
        d
    } else if mutation_kind == 2 {
        // set last element to max boundary (1000)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1000);
        d
    } else if mutation_kind == 3 {
        // set all elements to 2
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 2i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 2);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 100 {
        // grow by one element
        let mut d = nums;
        d.push(2);
        d
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by one element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge last element up (if < 1000)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 1000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge last element down (if > 2)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 2 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 8 {
        // set first element to 2
        let mut d = nums;
        d.set(0, 2);
        d
    } else if mutation_kind == 9 {
        // set first element to 1000
        let mut d = nums;
        d.set(0, 1000);
        d
    } else {
        nums // fallback
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
    generate_candidate(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(2, 1000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3314);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let nums = generate_test_case(nums);
        let key = format!("{:?}", nums);
        if *count >= target || !seen.insert(key) {
            return;
        }
        let output = Solution::min_bitwise_array(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let seeds: Vec<Vec<i32>> = vec![
        vec![2, 3, 5, 7],
        vec![11, 13, 31],
        // boundary and special cases
        vec![2],
        vec![1000],
        vec![2, 2, 2],
        vec![3],
        vec![5],
        vec![7],
        vec![997],
        vec![2, 1000],
        vec![1000, 2],
        vec![3, 5, 7, 11, 13],
        vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    for i in 0..60 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 3),     // tiny
            1 => rng.gen_range_usize(1, 10),    // small
            2 => rng.gen_range_usize(11, 50),   // medium
            3 => rng.gen_range_usize(51, 100),  // large
            _ => 100,                            // max
        };
        let seed = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let seed = random_nums(&mut rng, len);
        emit(mutate(seed, 0), &mut seen, &mut out, &mut count);
    }
}
