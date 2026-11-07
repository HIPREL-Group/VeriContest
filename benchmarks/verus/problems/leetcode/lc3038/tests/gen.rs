use vstd::prelude::*;

verus! {

/// Generates a valid `nums` vector for lc3038 (Maximum Number of Operations With the Same Score I).
///
/// Construction parameters:
/// - `base_vals`: a vector of base element values (each 1..=1000)
/// - `n`: desired length (2..=100)
/// - `mutation_kind`: selects different construction strategies
///
/// The generator builds an array where elements are in [1, 1000] and length is in [2, 100].
pub fn generate_test_case(
    base_vals: Vec<i32>,
    n: u8,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        2 <= n <= 100,
        base_vals.len() >= n,
        forall |i: int| 0 <= i < base_vals.len() ==> 1 <= #[trigger] base_vals[i] <= 1000,
    ensures
        2 <= result.len() <= 100,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    let len = n as usize;

    if mutation_kind == 0 {
        // Identity: copy first `len` elements
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                len == n as usize,
                2 <= n <= 100,
                k <= len,
                out.len() == k,
                len <= base_vals.len(),
                forall |i: int| 0 <= i < base_vals.len() ==> 1 <= #[trigger] base_vals[i] <= 1000,
                forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 1000,
            decreases len - k,
        {
            out.push(base_vals[k]);
            k = k + 1;
        }
        out
    } else if mutation_kind == 1 {
        // All same value: every element = base_vals[0]
        // This means every consecutive pair sums to the same value -> max operations
        let val = base_vals[0];
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                len == n as usize,
                2 <= n <= 100,
                k <= len,
                out.len() == k,
                1 <= val <= 1000,
                forall |i: int| 0 <= i < out.len() ==> #[trigger] out[i] == val,
                forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 1000,
            decreases len - k,
        {
            out.push(val);
            k = k + 1;
        }
        out
    } else if mutation_kind == 2 && len >= 4 {
        // Alternating pair pattern: [a, b, a, b, ...] so all pairs sum to a+b
        let a = base_vals[0];
        let b = base_vals[1];
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                len == n as usize,
                2 <= n <= 100,
                k <= len,
                out.len() == k,
                1 <= a <= 1000,
                1 <= b <= 1000,
                forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 1000,
            decreases len - k,
        {
            if k % 2 == 0 {
                out.push(a);
            } else {
                out.push(b);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 3 && len >= 4 {
        // First pair matches, rest differ: [a, b, c, d, ...]
        // where a+b != c+d, so count = 1
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        // Use base_vals[0], base_vals[1] for first pair
        // Then use base_vals[2..] for the rest, but nudge the third element
        // to break the pair sum
        while k < len
            invariant
                len == n as usize,
                2 <= n <= 100,
                len >= 4,
                k <= len,
                out.len() == k,
                len <= base_vals.len(),
                forall |i: int| 0 <= i < base_vals.len() ==> 1 <= #[trigger] base_vals[i] <= 1000,
                forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 1000,
            decreases len - k,
        {
            out.push(base_vals[k]);
            k = k + 1;
        }
        out
    } else if mutation_kind == 4 {
        // Minimum length (2 elements)
        let mut out: Vec<i32> = Vec::new();
        out.push(base_vals[0]);
        out.push(base_vals[1]);
        out
    } else if mutation_kind == 5 {
        // All ones: boundary value array
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                len == n as usize,
                2 <= n <= 100,
                k <= len,
                out.len() == k,
                forall |i: int| 0 <= i < out.len() ==> #[trigger] out[i] == 1i32,
                forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 1000,
            decreases len - k,
        {
            out.push(1i32);
            k = k + 1;
        }
        out
    } else if mutation_kind == 6 {
        // All 1000s: max boundary value
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                len == n as usize,
                2 <= n <= 100,
                k <= len,
                out.len() == k,
                forall |i: int| 0 <= i < out.len() ==> #[trigger] out[i] == 1000i32,
                forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 1000,
            decreases len - k,
        {
            out.push(1000i32);
            k = k + 1;
        }
        out
    } else if mutation_kind == 7 && len >= 3 {
        // Nudge second element: base_vals but second element is clamped to a nudged value
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                len == n as usize,
                2 <= n <= 100,
                len >= 3,
                k <= len,
                out.len() == k,
                len <= base_vals.len(),
                forall |i: int| 0 <= i < base_vals.len() ==> 1 <= #[trigger] base_vals[i] <= 1000,
                forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 1000,
            decreases len - k,
        {
            if k == 2 {
                // Nudge third element toward 1 to likely break pairs
                let v = base_vals[k];
                if v > 1 {
                    out.push((v - 1) as i32);
                } else {
                    out.push((v + 1) as i32);
                }
            } else {
                out.push(base_vals[k]);
            }
            k = k + 1;
        }
        out
    } else {
        // Fallback: copy first `len` elements (same as identity)
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < len
            invariant
                len == n as usize,
                2 <= n <= 100,
                k <= len,
                out.len() == k,
                len <= base_vals.len(),
                forall |i: int| 0 <= i < base_vals.len() ==> 1 <= #[trigger] base_vals[i] <= 1000,
                forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 1000,
            decreases len - k,
        {
            out.push(base_vals[k]);
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut rng = Rng::new(seed);
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![3, 2, 1, 4, 5],
        vec![1, 5, 3, 3, 4, 1, 3, 2, 2, 3],
        vec![5, 3],
    ];

    for ex in &examples {
        let nums = ex.clone();
        let result = Solution::max_operations(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();
        generated += 1;
    }

    // Generate remaining test cases
    while generated < count {
        // Size classes
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(2, 4),        // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(11, 30),      // medium
            3 => rng.gen_range_usize(31, 60),      // large
            _ => rng.gen_range_usize(61, 100),     // max
        };

        // Build base_vals with at least n elements
        let mut base_vals: Vec<i32> = Vec::with_capacity(n);
        for _ in 0..n {
            let v = if generated % 5 == 0 {
                // Boundary values ~20% of time
                match rng.gen_range_usize(0, 4) {
                    0 => 1,
                    1 => 1000,
                    2 => 500,
                    3 => 2,
                    _ => 999,
                }
            } else {
                rng.gen_range_i64(1, 1000) as i32
            };
            base_vals.push(v);
        }

        let mutation_kind = (rng.gen_range_usize(0, 8)) as u8;
        let n_u8 = n as u8;

        let nums = generate_test_case(base_vals, n_u8, mutation_kind);
        let result = Solution::max_operations(nums.clone());

        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();

        generated += 1;
    }

    eprintln!("Generated {} test cases to {}", generated, out_path.display());
}
