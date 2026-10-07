use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn div_count_from(n: int, d: int) -> int
        decreases n - d + 1
    {
        if d <= 0 || d > n { 0 }
        else if n % d == 0 { 1 + Self::div_count_from(n, d + 1) }
        else { Self::div_count_from(n, d + 1) }
    }

    pub open spec fn div_sum_from(n: int, d: int) -> int
        decreases n - d + 1
    {
        if d <= 0 || d > n { 0 }
        else if n % d == 0 { d + Self::div_sum_from(n, d + 1) }
        else { Self::div_sum_from(n, d + 1) }
    }

    pub open spec fn four_div_sum(nums: Seq<i32>, i: int) -> int
        decreases nums.len() - i
    {
        if i < 0 || i >= nums.len() { 0 }
        else if Self::div_count_from(nums[i] as int, 1) == 4 {
            Self::div_sum_from(nums[i] as int, 1) + Self::four_div_sum(nums, i + 1)
        }
        else { Self::four_div_sum(nums, i + 1) }
    }

    // 1 has exactly 1 divisor, not 4
    proof fn div_count_one()
        ensures
            Self::div_count_from(1, 1) == 1,
    {
        reveal_with_fuel(Solution::div_count_from, 3);
    }

    proof fn four_div_sum_all_ones(nums: Seq<i32>, i: int)
        requires
            0 <= i <= nums.len(),
            forall |j: int| 0 <= j < nums.len() ==> nums[j] == 1i32,
        ensures
            Self::four_div_sum(nums, i) == 0,
        decreases nums.len() - i,
    {
        if i < nums.len() {
            assert(nums[i] == 1i32);
            Self::div_count_one();
            reveal_with_fuel(Solution::four_div_sum, 2);
            Self::four_div_sum_all_ones(nums, i + 1);
        }
    }

    pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            0 <= Self::four_div_sum(nums@, 0) <= i32::MAX as int,
        ensures
            1 <= result.len() <= 10_000,
            forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100_000,
            0 <= Self::four_div_sum(result@, 0) <= i32::MAX as int,
    {
        if mutation_kind == 0 {
            // identity
            nums
        } else if mutation_kind == 1 {
            // set all elements to 1 => four_div_sum = 0
            let len = nums.len();
            let mut result: Vec<i32> = Vec::new();
            let mut idx: usize = 0;
            while idx < len
                invariant
                    0 <= idx <= len,
                    1 <= len <= 10_000,
                    result.len() == idx,
                    forall |j: int| 0 <= j < idx ==> result[j] == 1i32,
                decreases len - idx,
            {
                result.push(1i32);
                idx += 1;
            }
            assert(result.len() == len);
            proof {
                assert(forall |j: int| 0 <= j < result@.len() ==> result@[j] == 1i32);
                Self::four_div_sum_all_ones(result@, 0);
            }
            result
        } else if mutation_kind == 2 {
            // set all elements to 1 (alternate mutation for diversity in main)
            let len = nums.len();
            let mut result: Vec<i32> = Vec::new();
            let mut idx: usize = 0;
            while idx < len
                invariant
                    0 <= idx <= len,
                    1 <= len <= 10_000,
                    result.len() == idx,
                    forall |j: int| 0 <= j < idx ==> result[j] == 1i32,
                decreases len - idx,
            {
                result.push(1i32);
                idx += 1;
            }
            proof {
                Self::four_div_sum_all_ones(result@, 0);
            }
            result
        } else {
            // fallback: identity
            nums
        }
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

include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    nums
}

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    Solution::generate_test_case(nums, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1390);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::sum_four_divisors(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![21, 4, 7],
        vec![21, 21],
        vec![1, 2, 3, 4, 5],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2];

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut emitted);
        }
    }

    // Seed pool with interesting values
    let interesting_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![6],
        vec![8],
        vec![10],
        vec![100_000],
        vec![1, 1, 1, 1, 1],
        vec![6, 10, 14, 15, 21],
        vec![2, 3, 5, 7, 11],
        vec![4, 9, 25, 49],
        vec![12, 18, 24, 36],
        vec![6, 1, 10, 2, 21],
    ];

    for seed_arr in &interesting_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut emitted);
        }
    }

    // Size class random generation
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // very large
        };
        let nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 2) as u8;
        let result = mutate(nums, mk);
        emit(result, &mut seen, &mut out, &mut emitted);
    }
}
