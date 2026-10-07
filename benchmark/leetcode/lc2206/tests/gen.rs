use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        nums.len() % 2 == 0,
        2 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 500,
    ensures
        result.len() % 2 == 0,
        2 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 500,
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
        // set last element to 500 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 500);
        d
    } else if mutation_kind == 3 {
        // set all elements to the first element's value (all pairs)
        let mut d = nums;
        let val = d[0];
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == nums.len(),
                nums.len() % 2 == 0,
                2 <= d.len() <= 1000,
                1 <= val <= 500,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] d[j] <= 500,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 500,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() >= 4 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 5 {
        // nudge last element up (if < 500)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 500 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 6 {
        // nudge last element down (if > 1)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 7 && nums.len() <= 998 {
        // grow by 2 elements (maintain even length)
        let mut d = nums;
        d.push(1);
        d.push(1);
        d
    } else if mutation_kind == 8 && nums.len() > 2 {
        // shrink by 2 elements (maintain even length)
        let mut d = nums;
        d.pop();
        d.pop();
        d
    } else if mutation_kind == 9 {
        // set first element to 250 (mid-range)
        let mut d = nums;
        d.set(0, 250);
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
        nums.push(rng.gen_range_i64(1, 500) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2206);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::divide_array(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Hand-crafted seeds from problem examples and edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![3, 2, 3, 2, 2, 2],              // example 1: true
        vec![1, 2, 3, 4],                      // example 2: false
        vec![1, 1],                            // minimal even length, all pairs
        vec![1, 2],                            // minimal even length, no pairs
        vec![500, 500, 1, 1],                  // boundary values
        vec![250, 250, 250, 250],              // all same mid-range
        vec![1, 1, 2, 2, 3, 3, 4, 4, 5, 5],   // sequential pairs
        vec![1, 2, 3, 4, 5, 6, 7, 8],         // all distinct, false
        vec![500, 500],                        // max value pair
        vec![1, 1, 1, 1, 1, 1],               // all ones
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Size classes for diverse array lengths (all even)
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 4),       // tiny
        (6, 20),      // small
        (22, 100),    // medium
        (102, 500),   // large
        (502, 1000),  // max
    ];

    // Random seeds with random mutations across size classes
    for class_idx in 0..size_classes.len() {
        let (lo, hi) = size_classes[class_idx];
        for _ in 0..10 {
            let mut len = rng.gen_range_usize(lo, hi);
            if len % 2 != 0 { len += 1; }
            if len > 1000 { len = 1000; }
            let s = random_nums(&mut rng, len);
            let mk = rng.gen_range_usize(0, 9) as u8;
            let result = mutate(s, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random seeds, identity mutation
    while count < target_count {
        let mut len = rng.gen_range_usize(2, 1000);
        if len % 2 != 0 { len += 1; }
        if len > 1000 { len = 1000; }
        let s = random_nums(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
