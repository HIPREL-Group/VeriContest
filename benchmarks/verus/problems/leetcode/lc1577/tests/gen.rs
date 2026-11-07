use vstd::prelude::*;

verus! {

/// Constructs a valid pair of `Vec<i32>` for num_triplets from seed element
/// vectors, applying mutation_kind to diversify the generated inputs.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — set all elements of nums1 to the same value (elems1[0])
///   2 — set all elements of nums2 to the same value (elems2[0])
///   3 — nudge first element of nums1 up (if < 100_000)
///   4 — nudge first element of nums2 down (if > 1)
///   5 — set all elements of nums1 to 1 (min boundary)
///   6 — set all elements of nums2 to 100_000 (max boundary)
///   7 — swap first and last elements of nums1
pub fn generate_test_case(
    elems1: &Vec<i32>,
    elems2: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= elems1.len() <= 1000,
        1 <= elems2.len() <= 1000,
        forall |i: int| 0 <= i < elems1.len() ==> 1 <= #[trigger] elems1[i] <= 100_000,
        forall |i: int| 0 <= i < elems2.len() ==> 1 <= #[trigger] elems2[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1.len() <= 1000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100_000,
{
    let n1 = elems1.len();
    let n2 = elems2.len();

    if mutation_kind == 1 {
        // all elements of nums1 = elems1[0]
        let val = elems1[0];
        let mut out1: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n1
            invariant
                0 <= k <= n1,
                n1 == elems1.len(),
                1 <= n1 <= 1000,
                1 <= val <= 100_000,
                out1.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out1[j] == val,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out1[j] <= 100_000,
            decreases n1 - k,
        {
            out1.push(val);
            k = k + 1;
        }
        let out2 = copy_vec(elems2);
        (out1, out2)
    } else if mutation_kind == 2 {
        // all elements of nums2 = elems2[0]
        let val = elems2[0];
        let out1 = copy_vec(elems1);
        let mut out2: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n2
            invariant
                0 <= k <= n2,
                n2 == elems2.len(),
                1 <= n2 <= 1000,
                1 <= val <= 100_000,
                out2.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out2[j] == val,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out2[j] <= 100_000,
            decreases n2 - k,
        {
            out2.push(val);
            k = k + 1;
        }
        (out1, out2)
    } else if mutation_kind == 3 {
        // nudge first element of nums1 up
        let mut out1: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n1
            invariant
                0 <= k <= n1,
                n1 == elems1.len(),
                1 <= n1 <= 1000,
                out1.len() == k,
                forall |i: int| 0 <= i < elems1.len() ==> 1 <= #[trigger] elems1[i] <= 100_000,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out1[j] <= 100_000,
            decreases n1 - k,
        {
            if k == 0 && elems1[0] < 100_000 {
                out1.push(elems1[0] + 1);
            } else {
                out1.push(elems1[k]);
            }
            k = k + 1;
        }
        let out2 = copy_vec(elems2);
        (out1, out2)
    } else if mutation_kind == 4 {
        // nudge first element of nums2 down
        let out1 = copy_vec(elems1);
        let mut out2: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n2
            invariant
                0 <= k <= n2,
                n2 == elems2.len(),
                1 <= n2 <= 1000,
                out2.len() == k,
                forall |i: int| 0 <= i < elems2.len() ==> 1 <= #[trigger] elems2[i] <= 100_000,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out2[j] <= 100_000,
            decreases n2 - k,
        {
            if k == 0 && elems2[0] > 1 {
                out2.push(elems2[0] - 1);
            } else {
                out2.push(elems2[k]);
            }
            k = k + 1;
        }
        (out1, out2)
    } else if mutation_kind == 5 {
        // all elements of nums1 = 1 (min boundary)
        let mut out1: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n1
            invariant
                0 <= k <= n1,
                n1 == elems1.len(),
                1 <= n1 <= 1000,
                out1.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out1[j] == 1i32,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out1[j] <= 100_000,
            decreases n1 - k,
        {
            out1.push(1i32);
            k = k + 1;
        }
        let out2 = copy_vec(elems2);
        (out1, out2)
    } else if mutation_kind == 6 {
        // all elements of nums2 = 100_000 (max boundary)
        let out1 = copy_vec(elems1);
        let mut out2: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n2
            invariant
                0 <= k <= n2,
                n2 == elems2.len(),
                1 <= n2 <= 1000,
                out2.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out2[j] == 100_000i32,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out2[j] <= 100_000,
            decreases n2 - k,
        {
            out2.push(100_000i32);
            k = k + 1;
        }
        (out1, out2)
    } else if mutation_kind == 7 && n1 >= 2 {
        // swap first and last elements of nums1
        let mut out1: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n1
            invariant
                0 <= k <= n1,
                n1 == elems1.len(),
                1 <= n1 <= 1000,
                n1 >= 2,
                out1.len() == k,
                forall |i: int| 0 <= i < elems1.len() ==> 1 <= #[trigger] elems1[i] <= 100_000,
                forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out1[j] <= 100_000,
            decreases n1 - k,
        {
            if k == 0 {
                out1.push(elems1[n1 - 1]);
            } else if k == n1 - 1 {
                out1.push(elems1[0]);
            } else {
                out1.push(elems1[k]);
            }
            k = k + 1;
        }
        let out2 = copy_vec(elems2);
        (out1, out2)
    } else {
        // identity (mutation_kind == 0 or fallback)
        let out1 = copy_vec(elems1);
        let out2 = copy_vec(elems2);
        (out1, out2)
    }
}

/// Helper: copy a Vec<i32> preserving element bounds.
fn copy_vec(src: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= src.len() <= 1000,
        forall |i: int| 0 <= i < src.len() ==> 1 <= #[trigger] src[i] <= 100_000,
    ensures
        result.len() == src.len(),
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100_000,
{
    let mut out: Vec<i32> = Vec::new();
    let n = src.len();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == src.len(),
            1 <= n <= 1000,
            out.len() == k,
            forall |i: int| 0 <= i < src.len() ==> 1 <= #[trigger] src[i] <= 100_000,
            forall |j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 100_000,
        decreases n - k,
    {
        out.push(src[k]);
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

fn random_elems(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1577);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums1: Vec<i32>, nums2: Vec<i32>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}|{:?}", nums1, nums2);
        if !seen.insert(key) { return; }
        let result = Solution::num_triplets(nums1.clone(), nums2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2},
            "output": result
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    // Example 1: nums1 = [7,4], nums2 = [5,2,8,9] -> 1
    {
        let e1 = vec![7, 4];
        let e2 = vec![5, 2, 8, 9];
        for mk in 0u8..=7 {
            let (n1, n2) = generate_test_case(&e1, &e2, mk);
            emit(n1, n2, &mut seen, &mut out, &mut count);
        }
    }

    // Example 2: nums1 = [1,1], nums2 = [1,1,1] -> 9
    {
        let e1 = vec![1, 1];
        let e2 = vec![1, 1, 1];
        for mk in 0u8..=7 {
            let (n1, n2) = generate_test_case(&e1, &e2, mk);
            emit(n1, n2, &mut seen, &mut out, &mut count);
        }
    }

    // Example 3: nums1 = [7,7,8,3], nums2 = [1,2,9,7] -> 2
    {
        let e1 = vec![7, 7, 8, 3];
        let e2 = vec![1, 2, 9, 7];
        for mk in 0u8..=7 {
            let (n1, n2) = generate_test_case(&e1, &e2, mk);
            emit(n1, n2, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single element each
    {
        let e1 = vec![100_000];
        let e2 = vec![1];
        for mk in 0u8..=7 {
            let (n1, n2) = generate_test_case(&e1, &e2, mk);
            emit(n1, n2, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: boundary values
    {
        let e1 = vec![1, 1];
        let e2 = vec![100_000, 100_000];
        for mk in 0u8..=7 {
            let (n1, n2) = generate_test_case(&e1, &e2, mk);
            emit(n1, n2, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
    while count < target_count {
        let n1: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,                                  // single element
            1 => rng.gen_range_usize(2, 5),          // tiny
            2 => rng.gen_range_usize(6, 50),         // small
            3 => rng.gen_range_usize(51, 200),       // medium
            _ => rng.gen_range_usize(201, 1000),     // large
        };
        let n2: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,                                  // single element
            1 => rng.gen_range_usize(2, 5),          // tiny
            2 => rng.gen_range_usize(6, 50),         // small
            3 => rng.gen_range_usize(51, 200),       // medium
            _ => rng.gen_range_usize(201, 1000),     // large
        };

        // ~20% boundary-heavy inputs
        let e1 = if rng.gen_range_usize(0, 4) == 0 {
            let boundary_vals = [1i32, 2, 100, 1000, 100_000];
            let mut v = Vec::with_capacity(n1);
            for _ in 0..n1 {
                v.push(boundary_vals[rng.gen_range_usize(0, boundary_vals.len() - 1)]);
            }
            v
        } else {
            random_elems(&mut rng, n1)
        };

        let e2 = if rng.gen_range_usize(0, 4) == 0 {
            let boundary_vals = [1i32, 2, 100, 1000, 100_000];
            let mut v = Vec::with_capacity(n2);
            for _ in 0..n2 {
                v.push(boundary_vals[rng.gen_range_usize(0, boundary_vals.len() - 1)]);
            }
            v
        } else {
            random_elems(&mut rng, n2)
        };

        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (nums1, nums2) = generate_test_case(&e1, &e2, mk);
        emit(nums1, nums2, &mut seen, &mut out, &mut count);
    }
}
