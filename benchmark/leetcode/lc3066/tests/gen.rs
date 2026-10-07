use vstd::prelude::*;

verus! {

/// Constructs a valid `Vec<i32>` for min_operations from seed elements,
/// applying mutation_kind to diversify the generated inputs.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — set all elements to 1 (min boundary)
///   2 — set all elements to 1_000_000_000 (max boundary)
///   3 — nudge first element up: if < 1_000_000_000, increment by 1
///   4 — nudge first element down: if > 1, decrement by 1
///   5 — set last element to 1 (min boundary element)
///   6 — set last element to 1_000_000_000 (max boundary element)
///   7 — swap first and last elements
pub fn generate_test_case(
    seed_nums: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        2 <= seed_nums.len() <= 200_000,
        forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
        1 <= k <= 1_000_000_000,
    ensures
        2 <= nums.len() <= 200_000,
        1 <= k <= 1_000_000_000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = seed_nums.len();
    if mutation_kind == 1 {
        // set all elements to 1
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |idx: int| 0 <= idx < j ==> #[trigger] out[idx] == 1i32,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            out.push(1);
            j = j + 1;
        }
        out
    } else if mutation_kind == 2 {
        // set all elements to 1_000_000_000
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |idx: int| 0 <= idx < j ==> #[trigger] out[idx] == 1_000_000_000i32,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            out.push(1_000_000_000);
            j = j + 1;
        }
        out
    } else if mutation_kind == 3 {
        // nudge first element up
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            if j == 0 && seed_nums[0] < 1_000_000_000 {
                out.push(seed_nums[0] + 1);
            } else {
                out.push(seed_nums[j]);
            }
            j = j + 1;
        }
        out
    } else if mutation_kind == 4 {
        // nudge first element down
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            if j == 0 && seed_nums[0] > 1 {
                out.push(seed_nums[0] - 1);
            } else {
                out.push(seed_nums[j]);
            }
            j = j + 1;
        }
        out
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            if j == n - 1 {
                out.push(1);
            } else {
                out.push(seed_nums[j]);
            }
            j = j + 1;
        }
        out
    } else if mutation_kind == 6 {
        // set last element to 1_000_000_000
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            if j == n - 1 {
                out.push(1_000_000_000);
            } else {
                out.push(seed_nums[j]);
            }
            j = j + 1;
        }
        out
    } else if mutation_kind == 7 {
        // swap first and last
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            if j == 0 {
                out.push(seed_nums[n - 1]);
            } else if j == n - 1 {
                out.push(seed_nums[0]);
            } else {
                out.push(seed_nums[j]);
            }
            j = j + 1;
        }
        out
    } else {
        // identity: copy as-is (mutation_kind == 0 or any other value)
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == seed_nums.len(),
                2 <= n <= 200_000,
                out.len() == j,
                forall |i: int| 0 <= i < seed_nums.len() ==> 1 <= #[trigger] seed_nums[i] <= 1_000_000_000,
                forall |idx: int| 0 <= idx < j ==> 1 <= #[trigger] out[idx] <= 1_000_000_000,
            decreases n - j,
        {
            out.push(seed_nums[j]);
            j = j + 1;
        }
        out
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

extern crate serde_json;
use serde_json::json;

fn mutate(seed_nums: Vec<i32>, k: i32, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(seed_nums, k, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3066);
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
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "k": k},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Hardcoded examples from the problem description
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![2, 11, 10, 1, 3], 10),
        (vec![1, 1, 2, 4, 9], 20),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // Seed inputs covering diverse cases
    let seed_inputs: Vec<Vec<i32>> = vec![
        vec![1, 1],
        vec![1_000_000_000, 1_000_000_000],
        vec![1, 1_000_000_000],
        vec![1_000_000_000, 1],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![100, 200, 300, 400, 500, 600, 700, 800, 900, 1000],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        vec![500_000_000, 500_000_000, 500_000_000],
        vec![1, 2],
    ];

    let k_values: Vec<i32> = vec![1, 2, 10, 100, 1000, 1_000_000, 1_000_000_000];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Generate mutations of seed inputs with various k values
    for seed_nums in &seed_inputs {
        for &k in &k_values {
            for &mk in &mutation_kinds {
                let result = mutate(seed_nums.clone(), k, mk);
                emit(result, k, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random test cases to fill remaining slots
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(21, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let nums = random_nums(&mut rng, n);
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = mutate(nums, k, mk);
        emit(result, k, &mut seen, &mut out, &mut count);
    }
}
