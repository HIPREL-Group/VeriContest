use vstd::prelude::*;

verus! {

// Copied from spec.rs
pub open spec fn valid_partition(nums: Seq<i32>, k: int) -> bool {
    1 <= k < nums.len()
    && (forall |a: int, b: int| #![trigger nums[a], nums[b]]
        0 <= a < k && k <= b < nums.len() ==> nums[a] <= nums[b])
}

/// Build a valid partitionable array by concatenating `left_vals` (all <= threshold)
/// with `right_vals` (all >= threshold).
pub fn generate_test_case(
    left_vals: &Vec<i32>,
    right_vals: &Vec<i32>,
    threshold: i32,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        1 <= left_vals.len(),
        1 <= right_vals.len(),
        left_vals.len() + right_vals.len() <= 100_000,
        0 <= threshold <= 1_000_000,
        forall|i: int| 0 <= i < left_vals.len()
            ==> 0 <= #[trigger] left_vals[i] <= threshold,
        forall|i: int| 0 <= i < right_vals.len()
            ==> threshold <= #[trigger] right_vals[i] <= 1_000_000,
    ensures
        2 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
        exists|k: int| valid_partition(nums@, k),
{
    let left_len: usize = left_vals.len();
    let right_len: usize = right_vals.len();

    let mut nums: Vec<i32> = Vec::new();

    // --- Copy left part ---
    let mut i: usize = 0;
    while i < left_len
        invariant
            0 <= i <= left_len,
            nums.len() == i,
            left_len == left_vals.len(),
            right_len == right_vals.len(),
            left_len + right_len <= 100_000,
            0 <= threshold <= 1_000_000,
            forall|j: int| 0 <= j < left_vals.len()
                ==> 0 <= #[trigger] left_vals[j] <= threshold,
            forall|j: int| 0 <= j < i as int
                ==> nums[j] == left_vals[j],
            forall|j: int| 0 <= j < i as int
                ==> 0 <= #[trigger] nums[j] <= threshold,
        decreases left_len - i,
    {
        nums.push(left_vals[i]);
        i += 1;
    }

    // --- Apply mutations to the left portion ---
    if mutation_kind == 1 && left_len >= 1 {
        // Set first left element to 0 (boundary)
        nums.set(0, 0);
    } else if mutation_kind == 2 && left_len >= 1 {
        // Set all left elements to threshold
        let mut j: usize = 0;
        while j < left_len
            invariant
                0 <= j <= left_len,
                nums.len() == left_len,
                left_len + right_len <= 100_000,
                0 <= threshold <= 1_000_000,
                forall|k: int| 0 <= k < j as int
                    ==> nums[k] == threshold,
                forall|k: int| j as int <= k < left_len as int
                    ==> 0 <= #[trigger] nums[k] <= threshold,
            decreases left_len - j,
        {
            nums.set(j, threshold);
            j += 1;
        }
    } else if mutation_kind == 3 && left_len >= 1 {
        // Set all left elements to 0 (min boundary)
        let mut j: usize = 0;
        while j < left_len
            invariant
                0 <= j <= left_len,
                nums.len() == left_len,
                left_len + right_len <= 100_000,
                0 <= threshold <= 1_000_000,
                forall|k: int| 0 <= k < j as int
                    ==> nums[k] == 0i32,
                forall|k: int| j as int <= k < left_len as int
                    ==> 0 <= #[trigger] nums[k] <= threshold,
            decreases left_len - j,
        {
            nums.set(j, 0);
            j += 1;
        }
    }

    // snapshot left length before appending right
    let left_snapshot: Ghost<usize> = Ghost(left_len);

    // --- Append right part ---
    let mut i2: usize = 0;
    while i2 < right_len
        invariant
            0 <= i2 <= right_len,
            nums.len() == left_len + i2,
            left_len >= 1,
            right_len >= 1,
            right_len == right_vals.len(),
            left_len + right_len <= 100_000,
            0 <= threshold <= 1_000_000,
            forall|j: int| 0 <= j < right_vals.len()
                ==> threshold <= #[trigger] right_vals[j] <= 1_000_000,
            forall|j: int| 0 <= j < left_len as int
                ==> 0 <= #[trigger] nums[j] <= threshold,
            forall|j: int| left_len as int <= j < (left_len + i2) as int
                ==> threshold <= #[trigger] nums[j] <= 1_000_000,
        decreases right_len - i2,
    {
        let val = right_vals[i2];
        nums.push(val);
        i2 += 1;
    }

    // --- Apply mutations to the right portion ---
    if mutation_kind == 4 && right_len >= 1 {
        // Set all right elements to 1_000_000 (max boundary)
        let mut j: usize = 0;
        while j < right_len
            invariant
                0 <= j <= right_len,
                nums.len() == left_len + right_len,
                left_len >= 1,
                right_len >= 1,
                left_len + right_len <= 100_000,
                0 <= threshold <= 1_000_000,
                forall|k: int| 0 <= k < left_len as int
                    ==> 0 <= #[trigger] nums[k] <= threshold,
                forall|k: int| left_len as int <= k < (left_len + j) as int
                    ==> nums[k] == 1_000_000i32,
                forall|k: int| (left_len + j) as int <= k < (left_len + right_len) as int
                    ==> threshold <= #[trigger] nums[k] <= 1_000_000,
            decreases right_len - j,
        {
            nums.set(left_len + j, 1_000_000);
            j += 1;
        }
    } else if mutation_kind == 5 && right_len >= 1 {
        // Set all right elements to threshold
        let mut j: usize = 0;
        while j < right_len
            invariant
                0 <= j <= right_len,
                nums.len() == left_len + right_len,
                left_len >= 1,
                right_len >= 1,
                left_len + right_len <= 100_000,
                0 <= threshold <= 1_000_000,
                forall|k: int| 0 <= k < left_len as int
                    ==> 0 <= #[trigger] nums[k] <= threshold,
                forall|k: int| left_len as int <= k < (left_len + j) as int
                    ==> nums[k] == threshold,
                forall|k: int| (left_len + j) as int <= k < (left_len + right_len) as int
                    ==> threshold <= #[trigger] nums[k] <= 1_000_000,
            decreases right_len - j,
        {
            nums.set(left_len + j, threshold);
            j += 1;
        }
    }

    // --- Prove the ensures ---
    let total = nums.len();

    proof {
        // All elements are in [0, 1_000_000]
        assert forall|j: int| 0 <= j < nums.len()
            implies 0 <= #[trigger] nums[j] <= 1_000_000 by {
            if j < left_len as int {
                assert(0 <= nums[j] <= threshold);
            } else {
                assert(threshold <= nums[j] <= 1_000_000);
            }
        };

        // Prove valid_partition at k = left_len
        let k = left_len as int;
        assert(1 <= k);
        assert(k < nums.len());

        assert forall|a: int, b: int|
            #![trigger nums[a], nums[b]]
            0 <= a < k && k <= b < nums.len()
            implies nums[a] <= nums[b] by {
            assert(0 <= nums[a] <= threshold);
            assert(threshold <= nums[b] <= 1_000_000);
        };

        assert(valid_partition(nums@, k));
    }

    nums
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

extern crate serde_json;
use serde_json::json;

fn random_vec(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(915);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= goal {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::partition_disjoint(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // --- Example inputs from description.md ---
    emit(vec![5, 0, 3, 8, 6], &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1, 0, 6, 12], &mut seen, &mut out, &mut count);

    // --- Structured seeds × mutations ---
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    // Hand-crafted seed sets (left, right, threshold)
    let seeds: Vec<(Vec<i32>, Vec<i32>, i32)> = vec![
        (vec![0], vec![0], 0),                              // all zeros
        (vec![1_000_000], vec![1_000_000], 1_000_000),      // all max
        (vec![0], vec![1_000_000], 500_000),                // min-max
        (vec![3, 1, 2], vec![5, 4], 3),                     // small mixed
        (vec![5, 5, 5], vec![5, 5], 5),                     // all equal
        (vec![0, 0, 0], vec![1], 0),                        // zeros then one
        (vec![1], vec![1, 1, 1], 1),                        // one then ones
        (vec![100, 50, 99], vec![100, 200, 300], 100),      // threshold boundary
    ];

    for (left, right, thr) in &seeds {
        for &mk in &mutation_kinds {
            let nums = generate_test_case(left, right, *thr, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // --- Random test cases with size classes ---
    while count < goal {
        let total_n = match count % 5 {
            0 => rng.gen_range_usize(2, 5),       // tiny
            1 => rng.gen_range_usize(2, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // very large
        };

        let left_len = rng.gen_range_usize(1, total_n - 1);
        let right_len = total_n - left_len;

        // Pick threshold with boundary bias
        let threshold = if count % 5 == 0 {
            // boundary values
            *[0i32, 1, 500_000, 999_999, 1_000_000]
                .get(rng.gen_range_usize(0, 4))
                .unwrap()
        } else {
            rng.gen_range_i64(0, 1_000_000) as i32
        };

        let left = random_vec(&mut rng, left_len, 0, threshold);
        let right = random_vec(&mut rng, right_len, threshold, 1_000_000);
        let mk = rng.gen_range_usize(0, 5) as u8;

        let nums = generate_test_case(&left, &right, threshold, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }
}
