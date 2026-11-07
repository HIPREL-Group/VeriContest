use vstd::prelude::*;

verus! {

/// Constructs a valid `Vec<i32>` for num_identical_pairs from seed elements,
/// applying mutation_kind to diversify the generated inputs.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — set all elements to the same value (maximizes good pairs)
///   2 — nudge first element: if < 100, increment by 1
///   3 — nudge first element: if > 1, decrement by 1
///   4 — set all elements to 1 (min boundary)
///   5 — set all elements to 100 (max boundary)
///   6 — swap first and last elements
///   7 — set last element equal to first (creates at least one good pair)
pub fn generate_test_case(
    elems: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= elems.len() <= 100,
        forall |i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    let mut out: Vec<i32> = Vec::new();
    let n = elems.len();

    if mutation_kind == 1 {
        // all same value (elems[0])
        let val = elems[0];
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                1 <= val <= 100,
                out.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out[j] == val,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 100,
            decreases n - k,
        {
            out.push(val);
            k = k + 1;
        }
        out
    } else if mutation_kind == 2 {
        // nudge first element up
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 100,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 100,
            decreases n - k,
        {
            if k == 0 && elems[0] < 100 {
                out.push(elems[0] + 1);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 3 {
        // nudge first element down
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 100,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 100,
            decreases n - k,
        {
            if k == 0 && elems[0] > 1 {
                out.push(elems[0] - 1);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 4 {
        // all ones (min boundary)
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out[j] == 1i32,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 100,
            decreases n - k,
        {
            out.push(1i32);
            k = k + 1;
        }
        out
    } else if mutation_kind == 5 {
        // all 100s (max boundary)
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out[j] == 100i32,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 100,
            decreases n - k,
        {
            out.push(100i32);
            k = k + 1;
        }
        out
    } else if mutation_kind == 6 && n >= 2 {
        // swap first and last elements
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                n >= 2,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 100,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 100,
            decreases n - k,
        {
            if k == 0 {
                out.push(elems[n - 1]);
            } else if k == n - 1 {
                out.push(elems[0]);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 7 && n >= 2 {
        // set last element equal to first (guarantees at least one good pair)
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                n >= 2,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 100,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 100,
            decreases n - k,
        {
            if k == n - 1 {
                out.push(elems[0]);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else {
        // identity (mutation_kind == 0 or fallback)
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 100,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 100,
            decreases n - k,
        {
            out.push(elems[k]);
            k = k + 1;
        }
        out
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

fn random_elems(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i64(1, 100) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1512);
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
        let result = Solution::num_identical_pairs(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    // Example 1: nums = [1,2,3,1,1,3] -> 4
    {
        let elems = vec![1, 2, 3, 1, 1, 3];
        for mk in 0u8..=7 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Example 2: nums = [1,1,1,1] -> 6
    {
        let elems = vec![1, 1, 1, 1];
        for mk in 0u8..=7 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Example 3: nums = [1,2,3] -> 0
    {
        let elems = vec![1, 2, 3];
        for mk in 0u8..=7 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single element
    {
        let elems = vec![50];
        for mk in 0u8..=7 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: two identical elements
    {
        let elems = vec![42, 42];
        for mk in 0u8..=7 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: boundary values
    {
        let elems = vec![1, 1];
        for mk in 0u8..=7 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }
    {
        let elems = vec![100, 100];
        for mk in 0u8..=7 {
            let nums = generate_test_case(&elems, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,                                // single element
            1 => rng.gen_range_usize(2, 5),        // tiny
            2 => rng.gen_range_usize(6, 20),       // small
            3 => rng.gen_range_usize(21, 60),      // medium
            _ => rng.gen_range_usize(61, 100),     // max
        };

        // ~20% boundary-heavy inputs (values near 1 or 100)
        let elems = if rng.gen_range_usize(0, 4) == 0 {
            let boundary_vals = [1i32, 2, 50, 99, 100];
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(boundary_vals[rng.gen_range_usize(0, boundary_vals.len() - 1)]);
            }
            v
        } else {
            random_elems(&mut rng, n)
        };

        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let nums = generate_test_case(&elems, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }
}
