use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: Vec<i32>,
    k: i32,
    big_val: i32,
    big_idx: usize,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= vals.len() <= 50,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1_000_000_000,
        1 <= k <= 1_000_000_000,
        k <= big_val <= 1_000_000_000,
        0 <= big_idx < vals.len(),
    ensures
        1 <= result.0.len() <= 50,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        exists|i: int| 0 <= i < result.0.len() && result.0[i] >= result.1,
{
    if mutation_kind == 0 {
        // identity: place big_val at big_idx
        let mut nums = vals;
        nums.set(big_idx, big_val);
        assert(nums[big_idx as int] >= k);
        (nums, k)
    } else if mutation_kind == 1 {
        // set k to 1 (easiest threshold)
        let mut nums = vals;
        nums.set(big_idx, big_val);
        assert(nums[big_idx as int] >= 1i32);
        (nums, 1i32)
    } else if mutation_kind == 2 && vals.len() < 50 {
        // grow: push big_val at end
        let mut nums = vals;
        nums.set(big_idx, big_val);
        nums.push(big_val);
        assert(nums[big_idx as int] >= k);
        (nums, k)
    } else if mutation_kind == 3 && vals.len() > 1 && big_idx < vals.len() - 1 {
        // shrink: pop last element (safe because big_idx is not last)
        let mut nums = vals;
        nums.set(big_idx, big_val);
        nums.pop();
        assert(nums[big_idx as int] >= k);
        (nums, k)
    } else if mutation_kind == 4 {
        // set all elements to big_val (all >= k)
        let mut nums = vals;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == vals.len(),
                1 <= nums.len() <= 50,
                forall|j: int| 0 <= j < i ==> nums[j] == big_val,
                forall|j: int| i <= j < nums.len() ==> nums[j] == vals[j],
                1 <= big_val <= 1_000_000_000,
            decreases nums.len() - i,
        {
            nums.set(i, big_val);
            i += 1;
        }
        assert(nums[0] == big_val);
        assert(nums[0] >= k);
        (nums, k)
    } else if mutation_kind == 5 {
        // set k = big_val (exact boundary: element equals threshold)
        let mut nums = vals;
        nums.set(big_idx, big_val);
        assert(nums[big_idx as int] >= big_val);
        (nums, big_val)
    } else if mutation_kind == 6 && big_val < 1_000_000_000 {
        // nudge big_val up by 1
        let new_val: i32 = big_val + 1;
        let mut nums = vals;
        nums.set(big_idx, new_val);
        assert(nums[big_idx as int] >= k);
        (nums, k)
    } else if mutation_kind == 7 && k > 1 {
        // nudge k down by 1
        let new_k: i32 = k - 1;
        let mut nums = vals;
        nums.set(big_idx, big_val);
        assert(nums[big_idx as int] >= new_k);
        (nums, new_k)
    } else {
        // fallback: identity
        let mut nums = vals;
        nums.set(big_idx, big_val);
        assert(nums[big_idx as int] >= k);
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

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_operations(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![2, 11, 10, 1, 3], 10),
        (vec![1, 1, 2, 4, 9], 1),
        (vec![1, 1, 2, 4, 9], 9),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // Seed arrays with mutation sweep
    let seed_configs: Vec<(Vec<i32>, i32, i32, usize)> = vec![
        (vec![5], 5, 5, 0),                                    // single element, k == element
        (vec![1], 1, 1, 0),                                    // min values
        (vec![1_000_000_000], 1, 1_000_000_000, 0),            // max element
        (vec![1, 2, 3, 4, 5], 3, 5, 4),                        // small sorted
        (vec![5, 4, 3, 2, 1], 3, 5, 0),                        // small reverse sorted
        (vec![1, 1, 1, 1, 1], 1, 1, 0),                        // all same, min
        (vec![10, 20, 30], 25, 30, 2),                         // big_val at end
        (vec![100, 1, 1, 1, 1], 100, 100, 0),                  // big_val at start
        (vec![1, 1, 500, 1, 1], 500, 500, 2),                  // big_val in middle
        (vec![999_999_999, 1_000_000_000], 1_000_000_000, 1_000_000_000, 1), // near-max values
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
    for (vals, k, big_val, big_idx) in &seed_configs {
        for &mk in &mutation_kinds {
            let (nums, k_out) = generate_test_case(vals.clone(), *k, *big_val, *big_idx, mk);
            emit(nums, k_out, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    while count < target_count {
        // Size class for array length
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,                                     // minimum
            1 => rng.gen_range_usize(1, 5),              // tiny
            2 => rng.gen_range_usize(6, 20),             // small
            3 => rng.gen_range_usize(21, 40),            // medium
            _ => rng.gen_range_usize(41, 50),            // max
        };

        let vals = random_array(&mut rng, n);

        // k with boundary mixing
        let k: i32 = if count % 5 == 0 {
            *[1i32, 1_000_000_000, 500_000_000].get(rng.gen_range_usize(0, 2)).unwrap()
        } else {
            rng.gen_range_i64(1, 1_000_000_000) as i32
        };

        let big_val: i32 = rng.gen_range_i64(k as i64, 1_000_000_000) as i32;
        let big_idx: usize = rng.gen_range_usize(0, n - 1);
        let mk: u8 = rng.gen_range_usize(0, 7) as u8;

        let (nums, k_out) = generate_test_case(vals, k, big_val, big_idx, mk);
        emit(nums, k_out, &mut seen, &mut out, &mut count);
    }
}
