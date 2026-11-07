use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100000,
    ensures
        1 <= result.len() <= 100000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() >= 2 {
        // set element at index 1 equal to element at index 0 (triggers adjacent-equal deletion)
        let mut d = nums;
        let v = d[0];
        d.set(1, v);
        d
    } else if mutation_kind == 2 && nums.len() < 100000 {
        // grow by one element
        let mut d = nums;
        d.push(0i32);
        d
    } else if mutation_kind == 3 && nums.len() > 1 {
        // shrink by one element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 4 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 5 {
        // set all elements to the same value (maximizes deletions)
        let mut d = nums;
        let v = d[0];
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100000,
            decreases d.len() - i,
        {
            d.set(i, v);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0i32);
        d
    } else if mutation_kind == 7 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0i32);
        d
    } else if mutation_kind == 8 && nums.len() >= 2 {
        // make all adjacent pairs equal (alternating pattern)
        let mut d = nums;
        let mut i: usize = 0;
        while i + 1 < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100000,
            decreases d.len() - i,
        {
            let v = d[i];
            d.set(i + 1, v);
            i += 2;
        }
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // make all adjacent pairs different by setting even indices to 0, odd to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100000,
            decreases d.len() - i,
        {
            if i % 2 == 0 {
                d.set(i, 0i32);
            } else {
                d.set(i, 1i32);
            }
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
        nums.push(rng.gen_range_i64(0, 100000) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2216);
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
        let output = Solution::min_deletion(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from problem description
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![1, 1, 2, 3, 5],
        vec![1, 1, 2, 2, 3, 3],
    ];

    // Apply every mutation to example seeds
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    for s in &example_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Interesting seed arrays
    let interesting_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 2],
        vec![1, 1],
        vec![0, 0, 0, 0],
        vec![1, 2, 3, 4, 5, 6],
        vec![1, 1, 1, 1, 1],
        vec![5, 5, 5, 5, 5, 5],
        vec![0],
        vec![100000, 0, 100000, 0],
        vec![1, 2, 1, 2, 1, 2, 1],
    ];

    for s in &interesting_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse sizes and random mutations
    for _ in 0..200 {
        if count >= target { break; }
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10000),  // very large
        };
        let s = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target {
        let len = rng.gen_range_usize(1, 5000);
        let s = random_nums(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
