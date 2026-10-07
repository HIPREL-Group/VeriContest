use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        assert forall|i: int, j: int| 0 <= i < j < d.len() implies d[i] != d[j] by {
            // After swapping indices 0 and last:
            // d[0] == old d[last], d[last] == old d[0], others unchanged
            // Distinctness is preserved because we just permuted values
            if i == 0 && j == last as int {
                // d[0] = old d[last], d[last] = old d[0], distinct since old 0 != old last
                assert(nums[0] != nums[last as int]);
            } else if i == 0 {
                // d[0] = old d[last], d[j] = old d[j] where j != 0 and j != last
                assert(nums[last as int] != nums[j]);
            } else if j == last as int {
                // d[i] = old d[i], d[last] = old d[0] where i != 0 and i != last
                assert(nums[i] != nums[0]);
            } else {
                // both unchanged
                assert(nums[i] != nums[j]);
            }
        }
        d
    } else if mutation_kind == 2 && nums.len() > 1 {
        // remove last element (shrink)
        let mut d = nums;
        d.pop();
        assert forall|i: int, j: int| 0 <= i < j < d.len() implies d[i] != d[j] by {
            assert(nums[i] != nums[j]);
        }
        d
    } else if mutation_kind == 3 && nums.len() >= 2 {
        // rotate left by 1: move first element to end
        let mut d: Vec<i32> = Vec::new();
        let n = nums.len();
        let mut idx: usize = 1;
        while idx < n
            invariant
                1 <= idx <= n,
                n == nums.len(),
                d.len() == idx - 1,
                1 <= n <= 100,
                forall|k: int| 0 <= k < d.len() ==> d[k] == nums[k + 1],
                forall|k: int| 0 <= k < d.len() ==> 1 <= #[trigger] d[k] <= 100,
                forall|i1: int| 0 <= i1 < nums.len() ==> 1 <= #[trigger] nums[i1] <= 100,
                forall|i1: int, j1: int| 0 <= i1 < j1 < nums.len() ==> nums[i1] != nums[j1],
            decreases n - idx,
        {
            d.push(nums[idx]);
            idx += 1;
        }
        d.push(nums[0]);
        assert(d.len() == n);
        // Prove distinctness of the rotated array
        assert forall|i: int, j: int| 0 <= i < j < d.len() implies d[i] != d[j] by {
            let last = (n - 1) as int;
            if j < last {
                // d[i] = nums[i+1], d[j] = nums[j+1], both from interior
                assert(nums[i + 1] != nums[j + 1]);
            } else if i < last && j == last {
                // d[i] = nums[i+1], d[last] = nums[0]
                assert(nums[i + 1] != nums[0]);
            }
        }
        assert forall|i: int| 0 <= i < d.len() implies 1 <= #[trigger] d[i] <= 100 by {
            if i < (n - 1) as int {
                assert(d[i] == nums[i + 1]);
            } else {
                assert(d[i] == nums[0]);
            }
        }
        d
    } else if mutation_kind == 4 && nums.len() >= 2 {
        // swap elements at index 0 and 1
        let mut d = nums;
        let v0 = d[0];
        let v1 = d[1];
        d.set(0, v1);
        d.set(1, v0);
        assert forall|i: int, j: int| 0 <= i < j < d.len() implies d[i] != d[j] by {
            if i == 0 && j == 1 {
                assert(nums[0] != nums[1]);
            } else if i == 0 {
                assert(nums[1] != nums[j]);
            } else if i == 1 {
                assert(nums[0] != nums[j]);
            } else if j == 1 {
                assert(nums[i] != nums[0]);
            } else {
                assert(nums[i] != nums[j]);
            }
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

/// Generate a random array of distinct integers in [1, 100] of given length.
fn random_distinct_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    assert!(len >= 1 && len <= 100);
    // Shuffle the pool [1..=100] and take the first `len` elements
    let mut pool: Vec<i32> = (1..=100).collect();
    // Fisher-Yates shuffle
    for i in (1..pool.len()).rev() {
        let j = rng.gen_range_usize(0, i);
        pool.swap(i, j);
    }
    pool.truncate(len);
    pool
}

/// Generate a sorted (ascending) array of distinct integers in [1, 100].
fn sorted_distinct_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = random_distinct_array(rng, len);
    arr.sort();
    arr
}

/// Generate a rotated sorted array (the kind that returns non-negative result).
fn rotated_sorted_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = sorted_distinct_array(rng, len);
    if len > 1 {
        let k = rng.gen_range_usize(0, len - 1);
        // Rotate right by k: last k elements go to front
        let split = len - k;
        let mut rotated = Vec::with_capacity(len);
        rotated.extend_from_slice(&arr[split..]);
        rotated.extend_from_slice(&arr[..split]);
        rotated
    } else {
        arr
    }
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2855);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::minimum_right_shifts(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![3, 4, 5, 1, 2],
        vec![1, 3, 5],
        vec![2, 1, 4],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut total);
    }

    // Boundary seeds
    let boundary_seeds: Vec<Vec<i32>> = vec![
        vec![1],                         // single element
        vec![100],                       // single max element
        vec![1, 2],                      // min length sorted
        vec![2, 1],                      // min length rotated
        vec![1, 2, 3, 4, 5],            // sorted
        vec![5, 1, 2, 3, 4],            // rotated by 1
        vec![4, 5, 1, 2, 3],            // rotated by 2
        vec![3, 1, 2],                   // unsortable
        vec![50, 51, 52, 1, 2, 3],      // rotated sorted
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    // Apply every mutation to boundary seeds
    for seed in &boundary_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Rotated sorted arrays (cases that return >= 0)
    for _ in 0..15 {
        let len = match rng.gen_range_usize(0, 4) {
            0 => 1,                                // min
            1 => rng.gen_range_usize(2, 5),        // tiny
            2 => rng.gen_range_usize(6, 20),       // small
            3 => rng.gen_range_usize(21, 50),      // medium
            _ => rng.gen_range_usize(51, 100),     // large
        };
        let arr = rotated_sorted_array(&mut rng, len);
        for &mk in &mutation_kinds {
            let result = mutate(arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Random arrays (diverse, likely unsortable => returns -1)
    for _ in 0..30 {
        let len = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(6, 20),
            3 => rng.gen_range_usize(21, 50),
            _ => rng.gen_range_usize(51, 100),
        };
        let arr = random_distinct_array(&mut rng, len);
        let mk = rng.gen_range_usize(0, 4) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut seen, &mut out, &mut total);
    }

    // Fill remaining with random arrays, identity mutation
    while total < count {
        let len = rng.gen_range_usize(1, 100);
        let arr = random_distinct_array(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut total);
    }
}
