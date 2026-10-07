use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set all elements to 1 (minimum boundary)
        let mut r = nums;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == nums.len(),
                1 <= r.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> r[j] == 1,
                forall|j: int| i <= j < r.len() ==> r[j] == nums[j],
                forall|j: int| i <= j < r.len() ==> 1 <= #[trigger] r[j] <= 100_000,
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        r
    } else if mutation_kind == 2 {
        // set all elements to 100_000 (maximum boundary)
        let mut r = nums;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == nums.len(),
                1 <= r.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> r[j] == 100_000,
                forall|j: int| i <= j < r.len() ==> r[j] == nums[j],
                forall|j: int| i <= j < r.len() ==> 1 <= #[trigger] r[j] <= 100_000,
            decreases r.len() - i,
        {
            r.set(i, 100_000);
            i += 1;
        }
        r
    } else if mutation_kind == 3 {
        // set first element to 1
        let mut r = nums;
        r.set(0, 1);
        r
    } else if mutation_kind == 4 {
        // set first element to 100_000
        let mut r = nums;
        r.set(0, 100_000);
        r
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut r = nums;
        let last = r.len() - 1;
        r.set(last, 1);
        r
    } else if mutation_kind == 6 {
        // set last element to 100_000
        let mut r = nums;
        let last = r.len() - 1;
        r.set(last, 100_000);
        r
    } else if mutation_kind == 7 && nums.len() < 100_000 {
        // grow: push element 1
        let mut r = nums;
        r.push(1);
        r
    } else if mutation_kind == 8 && nums.len() > 1 {
        // shrink: pop last element
        let mut r = nums;
        r.pop();
        r
    } else if mutation_kind == 9 {
        // nudge first element up (if < 100_000)
        let mut r = nums;
        if r[0] < 100_000 {
            r.set(0, r[0] + 1);
        }
        r
    } else if mutation_kind == 10 {
        // nudge first element down (if > 1)
        let mut r = nums;
        if r[0] > 1 {
            r.set(0, r[0] - 1);
        }
        r
    } else if mutation_kind == 11 && nums.len() >= 2 {
        // swap first and last elements
        let mut r = nums;
        let last = r.len() - 1;
        let tmp = r[0];
        r.set(0, r[last]);
        r.set(last, tmp);
        r
    } else if mutation_kind == 12 {
        // halve first element (max with 1)
        let mut r = nums;
        let half = r[0] / 2;
        if half >= 1 {
            r.set(0, half);
        } else {
            r.set(0, 1);
        }
        r
    } else if mutation_kind == 13 {
        // double first element (capped at 100_000)
        let mut r = nums;
        if r[0] <= 50_000 {
            r.set(0, r[0] * 2);
        } else {
            r.set(0, 100_000);
        }
        r
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
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1862);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Keep array sizes small for O(n²) code.rs
    let max_gen_size: usize = 200;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::sum_of_floored_pairs(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 5, 9],
        vec![7, 7, 7, 7, 7, 7, 7],
    ];

    let mutation_kinds: Vec<u8> = (0..=13).collect();

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Hand-crafted seeds covering interesting cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],                          // single element, minimum value
        vec![100_000],                    // single element, maximum value
        vec![1, 1],                       // all ones
        vec![1, 100_000],                 // min and max
        vec![100_000, 1],                 // max and min (reversed)
        vec![2, 3, 5, 7, 11],            // primes
        vec![1, 2, 4, 8, 16],            // powers of 2
        vec![10, 10, 10, 10],            // all equal
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], // consecutive
        vec![50_000, 50_000, 50_000],    // large equal values
    ];

    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations, varying sizes
    while count < count_target {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),            // tiny
            1 => rng.gen_range_usize(1, 10),            // small
            2 => rng.gen_range_usize(11, 50),           // medium
            3 => rng.gen_range_usize(51, max_gen_size),  // large
            _ => rng.gen_range_usize(1, max_gen_size),
        };
        let seed = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 13) as u8;
        let result = mutate(seed, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
