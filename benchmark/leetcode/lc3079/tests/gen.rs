use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set all elements to 1 (minimum boundary)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 2 {
        // set all elements to 1000 (maximum boundary)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 1000i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1000);
            i += 1;
        }
        d
    } else if mutation_kind == 3 && nums.len() > 1 {
        // shrink: drop the last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 4 && nums.len() < 50 {
        // grow: push value 500
        let mut d = nums;
        d.push(500);
        d
    } else if mutation_kind == 5 {
        // set first element to 999 (near-max boundary)
        let mut d = nums;
        d.set(0, 999);
        d
    } else if mutation_kind == 6 {
        // set last element to 1 (min boundary on last)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else {
        // fallback: identity
        nums
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1000) as i32);
    }
    v
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3079);
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
        let output = Solution::sum_of_encrypted_int(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from problem description
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3],
        vec![10, 21, 31],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Boundary seeds
    let boundary_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1000],
        vec![1; 50],
        vec![1000; 50],
        vec![9],
        vec![99],
        vec![999],
        vec![10],
        vec![100],
        vec![500, 500],
        vec![1, 1000],
        vec![123, 456, 789],
        vec![111, 222, 333, 444, 555],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to boundary seeds
    for seed in &boundary_seeds {
        for &mk in &mutation_kinds {
            if count >= target { break; }
            let result = generate_test_case(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations
    for _ in 0..200 {
        if count >= target { break; }
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),    // tiny
            1 => rng.gen_range_usize(1, 10),   // small
            2 => rng.gen_range_usize(11, 30),  // medium
            3 => rng.gen_range_usize(31, 50),  // large
            _ => rng.gen_range_usize(45, 50),  // max
        };
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = generate_test_case(nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 50);
        let nums = random_nums(&mut rng, len);
        emit(generate_test_case(nums, 0), &mut seen, &mut out, &mut count);
    }
}
