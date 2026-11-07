use vstd::prelude::*;

verus! {

/// Constructs a valid `Vec<i32>` for find_indices from seed elements,
/// applying mutation_kind to diversify the generated inputs.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — set all elements to 0
///   2 — set all elements to 1_000_000_000 (max boundary)
///   3 — nudge first element up: if < 1_000_000_000, increment by 1
///   4 — nudge first element down: if > 0, decrement by 1
///   5 — set last element to 0 (min boundary element)
///   6 — set last element to 1_000_000_000 (max boundary element)
///   7 — swap first and last elements
pub fn generate_test_case(
    elems: &Vec<i32>,
    index_difference: i32,
    value_difference: i32,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        1 <= elems.len() <= 100_000,
        forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1_000_000_000,
        0 <= index_difference <= 100_000,
        0 <= value_difference <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 100_000,
        0 <= index_difference <= 100_000,
        0 <= value_difference <= 1_000_000_000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = elems.len();

    if mutation_kind == 1 {
        // set all elements to 0
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out[j] == 0i32,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            out.push(0);
            k = k + 1;
        }
        out
    } else if mutation_kind == 2 {
        // set all elements to 1_000_000_000
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out[j] == 1_000_000_000i32,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            out.push(1_000_000_000);
            k = k + 1;
        }
        out
    } else if mutation_kind == 3 {
        // nudge first element up
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1_000_000_000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            if k == 0 && elems[0] < 1_000_000_000 {
                out.push(elems[0] + 1);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 4 {
        // nudge first element down
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1_000_000_000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            if k == 0 && elems[0] > 0 {
                out.push(elems[0] - 1);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 5 {
        // set last element to 0
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1_000_000_000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            if k == n - 1 {
                out.push(0);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 6 {
        // set last element to 1_000_000_000
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1_000_000_000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - k,
        {
            if k == n - 1 {
                out.push(1_000_000_000);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 7 && n > 1 {
        // swap first and last elements
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                n > 1,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1_000_000_000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
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
    } else {
        // identity (mutation_kind == 0 or fallback)
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1_000_000_000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
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

fn mutate(elems: &Vec<i32>, index_difference: i32, value_difference: i32, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(elems, index_difference, value_difference, mutation_kind)
}

fn random_elems(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1_000_000_000) as i32);
    }
    v
}

fn pick_i32(slice: &[i32], rng: &mut Rng) -> i32 {
    slice[rng.gen_range_usize(0, slice.len() - 1)]
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2905);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);
    let mut generated = 0usize;
    let num_mutations: u8 = 8;

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![5, 1, 4, 1], 2, 4),
        (vec![2, 1], 0, 0),
        (vec![1, 2, 3], 2, 4),
    ];

    for (nums, idx_diff, val_diff) in &examples {
        if generated >= count { break; }
        let result = Solution::find_indices(nums.clone(), *idx_diff, *val_diff);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "indexDifference": idx_diff, "valueDifference": val_diff},
            "output": result
        })).unwrap();
        generated += 1;
    }

    // Seed pool with interesting arrays
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1_000_000_000],
        vec![0, 1_000_000_000],
        vec![500_000_000, 500_000_000, 500_000_000],
        vec![0, 0, 0, 0, 0],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    ];

    // Generate from seed arrays x mutations x varied index/value differences
    for seed_arr in &seed_arrays {
        for mk in 0..num_mutations {
            if generated >= count { break; }

            let index_difference = rng.gen_range_i64(0, std::cmp::min(seed_arr.len() as i64, 100_000)) as i32;
            let value_difference = rng.gen_range_i64(0, 1_000_000_000) as i32;

            let nums = mutate(seed_arr, index_difference, value_difference, mk);
            let result = Solution::find_indices(nums.clone(), index_difference, value_difference);
            writeln!(out, "{}", json!({
                "input": {"nums": nums, "indexDifference": index_difference, "valueDifference": value_difference},
                "output": result
            })).unwrap();
            generated += 1;
        }
    }

    // Random test cases with size classes
    while generated < count {
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),          // tiny
            1 => rng.gen_range_usize(1, 10),          // small
            2 => rng.gen_range_usize(11, 100),         // medium
            3 => rng.gen_range_usize(101, 1000),       // large
            _ => rng.gen_range_usize(1001, 10_000),    // max-ish
        };

        let elems = random_elems(&mut rng, n);

        let index_difference = rng.gen_range_i64(0, std::cmp::min(n as i64, 100_000)) as i32;

        // Mix boundary values for value_difference
        let value_difference = if generated % 5 == 0 {
            pick_i32(&[0i32, 1, 1_000_000_000], &mut rng)
        } else {
            rng.gen_range_i64(0, 1_000_000_000) as i32
        };

        let mutation_kind = (rng.next_u64() % num_mutations as u64) as u8;
        let nums = mutate(&elems, index_difference, value_difference, mutation_kind);
        let result = Solution::find_indices(nums.clone(), index_difference, value_difference);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "indexDifference": index_difference, "valueDifference": value_difference},
            "output": result
        })).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {}", generated, out_path.display());
}
