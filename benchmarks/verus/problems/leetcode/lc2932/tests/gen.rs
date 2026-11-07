use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        // set last element to 100 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else if mutation_kind == 3 && nums.len() < 50 {
        // grow by one element (push 50)
        let mut d = nums;
        d.push(50);
        d
    } else if mutation_kind == 4 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 5 {
        // set all elements to a single value (42)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 42,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 42);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // nudge last element up: if < 100, increment by 1
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 100 {
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
    } else if mutation_kind == 8 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 9 {
        // set first element to 1
        let mut d = nums;
        d.set(0, 1);
        d
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2932);
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
        let output = Solution::maximum_strong_pair_xor(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 4, 5],
        vec![10, 100],
        vec![5, 6, 25, 30],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seed inputs
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100],
        vec![1, 1],
        vec![100, 100],
        vec![1, 100],
        vec![50, 50],
        vec![1, 2],
        vec![99, 100],
        vec![1, 2, 3],
        vec![50, 51, 52, 53],
        vec![1, 1, 1, 1, 1],
        vec![33, 66, 99],
        vec![7, 14, 28],
        vec![1, 3, 5, 7, 9, 11, 13, 15],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across diverse size classes
    for i in 0..200 {
        if count >= target { break; }
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 3),   // tiny
            1 => rng.gen_range_usize(1, 10),  // small
            2 => rng.gen_range_usize(11, 25), // medium
            3 => rng.gen_range_usize(26, 40), // large
            _ => rng.gen_range_usize(41, 50), // max
        };
        let s = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutations on random inputs
    while count < target {
        let len = rng.gen_range_usize(1, 50);
        let s = random_nums(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
