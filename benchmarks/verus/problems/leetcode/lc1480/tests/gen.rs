use vstd::prelude::*;

verus! {

/// Constructs a valid `Vec<i32>` from seed elements, applying mutation_kind
/// to diversify the generated inputs.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — negate each element
///   2 — all zeros
///   3 — all elements set to 1_000_000 (max boundary)
///   4 — all elements set to -1_000_000 (min boundary)
///   5 — absolute value of each element
pub fn generate_test_case(
    elems: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= elems.len() <= 1000,
        forall |i: int| 0 <= i < elems.len() ==> -1_000_000 <= #[trigger] elems[i] <= 1_000_000,
    ensures
        1 <= result.len() <= 1000,
        forall |i: int| 0 <= i < result.len() ==> -1_000_000 <= #[trigger] result[i] <= 1_000_000,
{
    let mut out: Vec<i32> = Vec::new();
    let n = elems.len();
    let mut k: usize = 0;

    while k < n
        invariant
            0 <= k <= n,
            n == elems.len(),
            1 <= n <= 1000,
            out.len() == k,
            forall |i: int| 0 <= i < elems.len() ==> -1_000_000 <= #[trigger] elems[i] <= 1_000_000,
            forall |j: int| 0 <= j < k ==> -1_000_000 <= #[trigger] out[j] <= 1_000_000,
        decreases n - k,
    {
        let val: i32 = if mutation_kind == 1 {
            // negate
            -elems[k]
        } else if mutation_kind == 2 {
            // all zeros
            0i32
        } else if mutation_kind == 3 {
            // max boundary
            1_000_000i32
        } else if mutation_kind == 4 {
            // min boundary
            -1_000_000i32
        } else if mutation_kind == 5 {
            // absolute value
            if elems[k] < 0 { -elems[k] } else { elems[k] }
        } else {
            // identity
            elems[k]
        };

        assert(-1_000_000 <= val <= 1_000_000);
        out.push(val);
        k = k + 1;
    }

    out
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

fn random_elems(rng: &mut Rng, n: usize, val_lo: i64, val_hi: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i64(val_lo, val_hi) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1480);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let result = Solution::running_sum(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();
        *count += 1;
    };

    // Example 1: nums = [1,2,3,4]
    {
        let elems = vec![1, 2, 3, 4];
        for mk in 0u8..=5 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Example 2: nums = [1,1,1,1,1]
    {
        let elems = vec![1, 1, 1, 1, 1];
        for mk in 0u8..=5 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Example 3: nums = [3,1,2,10,1]
    {
        let elems = vec![3, 1, 2, 10, 1];
        for mk in 0u8..=5 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single element
    {
        let elems = vec![0];
        for mk in 0u8..=5 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single element at boundaries
    {
        let elems = vec![1_000_000];
        for mk in 0u8..=5 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }
    {
        let elems = vec![-1_000_000];
        for mk in 0u8..=5 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };

        let val_lo: i64 = -1_000_000;
        let val_hi: i64 = 1_000_000;

        // ~20% boundary-heavy inputs
        let elems = if rng.gen_range_usize(0, 4) == 0 {
            let boundary_vals = [0i32, 1, -1, 1_000_000, -1_000_000];
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(boundary_vals[rng.gen_range_usize(0, boundary_vals.len() - 1)]);
            }
            v
        } else {
            random_elems(&mut rng, n, val_lo, val_hi)
        };

        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let nums = generate_test_case(&elems, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }
}
