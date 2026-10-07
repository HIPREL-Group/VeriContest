use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        2 <= nums.len() <= 100,
        1 < 2 * k as int,
        2 * k as int <= nums.len(),
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
    ensures
        2 <= result.0.len() <= 100,
        1 < 2 * result.1 as int,
        2 * result.1 as int <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> -1000 <= #[trigger] result.0[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 && nums[0] < 1000 {
        // nudge first element up
        let mut d = nums;
        d.set(0, d[0] + 1);
        (d, k)
    } else if mutation_kind == 2 && nums[0] > -1000 {
        // nudge first element down
        let mut d = nums;
        d.set(0, d[0] - 1);
        (d, k)
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0);
        (d, k)
    } else if mutation_kind == 4 {
        // set first element to -1000 (min boundary)
        let mut d = nums;
        d.set(0, -1000);
        (d, k)
    } else if mutation_kind == 5 {
        // set first element to 1000 (max boundary)
        let mut d = nums;
        d.set(0, 1000);
        (d, k)
    } else if mutation_kind == 6 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        (d, k)
    } else if mutation_kind == 7 {
        // set k to 1 (minimum valid k)
        (nums, 1)
    } else if mutation_kind == 8 {
        // set k to max valid value (nums.len() / 2)
        let max_k = (nums.len() / 2) as i32;
        (nums, max_k)
    } else if mutation_kind == 9 {
        // set all elements to the same value (breaks strictly increasing)
        let val = nums[0];
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 100,
                -1000 <= val <= 1000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 10 {
        // set last element to -1000 (boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, -1000);
        (d, k)
    } else if mutation_kind == 11 {
        // set last element to 1000 (boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1000);
        (d, k)
    } else if mutation_kind == 12 && nums[0] > -1000 {
        // negate first element (if result in range)
        let mut d = nums;
        let neg = -d[0];
        if neg >= -1000 && neg <= 1000 {
            d.set(0, neg);
        }
        (d, k)
    } else {
        // fallback: identity
        (nums, k)
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    nums
}

fn make_increasing(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    let mut cur = rng.gen_range_i64(-1000, 1000 - len as i64) as i32;
    for _ in 0..len {
        nums.push(cur);
        cur += 1;
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let mut rng = Rng::new(3349);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let target = 100;
    let num_mutations: u8 = 13;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::has_increasing_subarrays(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description
    let example_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![2, 5, 7, 8, 9, 2, 3, 4, 3, 1], 3),
        (vec![1, 2, 3, 4, 4, 4, 4, 5, 6, 7], 5),
    ];

    for (nums, k) in &example_seeds {
        for mk in 0..num_mutations {
            let (res_nums, res_k) = generate_test_case(nums.clone(), *k, mk);
            emit(res_nums, res_k, &mut seen, &mut out, &mut count);
        }
    }

    // Hand-crafted seeds: strictly increasing arrays (should yield true)
    let crafted_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 2, 3, 4], 1),
        (vec![1, 2, 3, 4], 2),
        (vec![-5, -4, -3, -2, -1, 0], 3),
        (vec![0, 1], 1),
        (make_increasing(&mut rng, 10), 5),
        (make_increasing(&mut rng, 20), 10),
        (make_increasing(&mut rng, 100), 50),
        // all same values (should yield false)
        (vec![5, 5, 5, 5], 1),
        (vec![0, 0, 0, 0, 0, 0], 3),
        // decreasing (should yield false)
        (vec![10, 9, 8, 7, 6, 5], 3),
        (vec![1000, 999, 998, 997], 2),
        // boundaries
        (vec![-1000, -1000], 1),
        (vec![1000, 1000], 1),
        (vec![-1000, 1000], 1),
        (vec![1000, -1000], 1),
        // mixed patterns
        (vec![1, 2, 3, 1, 2, 3], 3),
        (vec![1, 2, 1, 2, 1, 2], 1),
        (vec![1, 3, 5, 2, 4, 6], 3),
    ];

    for (nums, k) in &crafted_seeds {
        for mk in 0..num_mutations {
            let (res_nums, res_k) = generate_test_case(nums.clone(), *k, mk);
            emit(res_nums, res_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across diverse size classes
    while count < target {
        let n: usize = match rng.next_u64() % 5 {
            0 => rng.gen_range_usize(2, 4),       // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(10, 30),      // medium
            3 => rng.gen_range_usize(30, 60),      // large
            _ => rng.gen_range_usize(60, 100),     // max-ish
        };
        let max_k = (n / 2) as i32;
        let k = rng.gen_range_i64(1, max_k as i64) as i32;
        let nums = random_nums(&mut rng, n);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (res_nums, res_k) = generate_test_case(nums, k, mk);
        emit(res_nums, res_k, &mut seen, &mut out, &mut count);
    }
}
