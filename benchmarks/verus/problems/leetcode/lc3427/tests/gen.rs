use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_vals: Vec<i32>,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        1 <= raw_vals.len() <= 100,
        forall |i: int| 0 <= i < raw_vals.len() ==> 1 <= #[trigger] raw_vals[i] <= 1000,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    if mutation_kind == 0 {
        // Identity: return raw_vals as-is
        raw_vals
    } else if mutation_kind == 1 && raw_vals.len() < 100 {
        // Grow: push one element (value 1)
        let mut result = raw_vals;
        result.push(1i32);
        result
    } else if mutation_kind == 2 && raw_vals.len() > 1 {
        // Shrink: pop last element
        let mut result = raw_vals;
        result.pop();
        result
    } else if mutation_kind == 3 {
        // Set all elements to 1 (minimum value)
        let len = raw_vals.len();
        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                0 <= k <= len,
                result.len() == k,
                len == raw_vals.len(),
                1 <= len <= 100,
                forall |j: int| 0 <= j < k ==> #[trigger] result[j] == 1i32,
            decreases len - k,
        {
            result.push(1i32);
            k += 1;
        }
        result
    } else if mutation_kind == 4 {
        // Set all elements to 1000 (maximum value)
        let len = raw_vals.len();
        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                0 <= k <= len,
                result.len() == k,
                len == raw_vals.len(),
                1 <= len <= 100,
                forall |j: int| 0 <= j < k ==> #[trigger] result[j] == 1000i32,
            decreases len - k,
        {
            result.push(1000i32);
            k += 1;
        }
        result
    } else if mutation_kind == 5 {
        // Nudge each element up by 1 (clamped to 1000)
        let len = raw_vals.len();
        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                0 <= k <= len,
                result.len() == k,
                len == raw_vals.len(),
                1 <= len <= 100,
                forall |i: int| 0 <= i < raw_vals.len() ==> 1 <= #[trigger] raw_vals[i] <= 1000,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] result[j] <= 1000,
            decreases len - k,
        {
            let v = raw_vals[k];
            if v < 1000 {
                result.push((v + 1) as i32);
            } else {
                result.push(v);
            }
            k += 1;
        }
        result
    } else if mutation_kind == 6 {
        // Nudge each element down by 1 (clamped to 1)
        let len = raw_vals.len();
        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                0 <= k <= len,
                result.len() == k,
                len == raw_vals.len(),
                1 <= len <= 100,
                forall |i: int| 0 <= i < raw_vals.len() ==> 1 <= #[trigger] raw_vals[i] <= 1000,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] result[j] <= 1000,
            decreases len - k,
        {
            let v = raw_vals[k];
            if v > 1 {
                result.push((v - 1) as i32);
            } else {
                result.push(v);
            }
            k += 1;
        }
        result
    } else if mutation_kind == 7 {
        // Reverse the array
        let len = raw_vals.len();
        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                0 <= k <= len,
                result.len() == k,
                len == raw_vals.len(),
                1 <= len <= 100,
                forall |i: int| 0 <= i < raw_vals.len() ==> 1 <= #[trigger] raw_vals[i] <= 1000,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] result[j] <= 1000,
            decreases len - k,
        {
            let idx = len - 1 - k;
            result.push(raw_vals[idx]);
            k += 1;
        }
        result
    } else {
        // Fallback: identity
        raw_vals
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

fn make_raw_vals(rng: &mut Rng, len: usize, val_lo: i64, val_hi: i64) -> Vec<i32> {
    let mut vals = Vec::new();
    for _ in 0..len {
        vals.push(rng.gen_range_i64(val_lo, val_hi) as i32);
    }
    vals
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    // Example 1 from description
    {
        let nums = vec![2i32, 3, 1];
        let result = Solution::subarray_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
    }
    // Example 2 from description
    {
        let nums = vec![3i32, 1, 1, 2];
        let result = Solution::subarray_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
    }

    let num_examples = 2;
    let remaining = if count > num_examples { count - num_examples } else { 0 };

    for i in 0..remaining {
        // Size classes
        let n: usize = match i % 6 {
            0 => 1,                                          // minimum
            1 => rng.gen_range_usize(1, 5),                  // tiny
            2 => rng.gen_range_usize(1, 10),                 // small
            3 => rng.gen_range_usize(11, 50),                // medium
            4 => rng.gen_range_usize(51, 99),                // large
            _ => 100,                                        // maximum
        };

        // Value distribution
        let (val_lo, val_hi): (i64, i64) = match i % 5 {
            0 => (1, 1),           // all ones
            1 => (1, 10),          // small values
            2 => (1, 100),         // medium values
            3 => (500, 1000),      // large values
            _ => (1, 1000),        // full range
        };

        let raw_vals = make_raw_vals(&mut rng, n, val_lo, val_hi);

        // Cycle through mutation kinds
        let mutation_kind = (i % 9) as u8;

        let nums = generate_test_case(raw_vals, mutation_kind);
        let result = Solution::subarray_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
    }
}
