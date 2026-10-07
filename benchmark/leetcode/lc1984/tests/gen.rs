use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 1000,
        1 <= k <= values.len(),
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= result.1 <= result.0.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < values.len()
        invariant
            0 <= i <= values.len(),
            nums.len() == i,
            1 <= values.len() <= 1000,
            forall|j: int| 0 <= j < values.len() ==> 0 <= #[trigger] values[j] <= 100_000,
            forall|j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 100_000,
        decreases values.len() - i,
    {
        let val: i32 =
            if mutation_kind == 1 {
                // All zeros
                0i32
            } else if mutation_kind == 2 {
                // All max
                100_000i32
            } else if mutation_kind == 3 {
                // All same as first element
                values[0]
            } else if mutation_kind == 4 && i == 0 && values[0usize] < 100_000 {
                // Nudge first element up
                (values[0usize] + 1) as i32
            } else if mutation_kind == 5 && i == 0 && values[0usize] > 0 {
                // Nudge first element down
                (values[0usize] - 1) as i32
            } else if mutation_kind == 6 && i == 0 {
                // Set first element to 0
                0i32
            } else if mutation_kind == 7 && i == 0 {
                // Set first element to 100_000
                100_000i32
            } else {
                // Identity (mutation_kind == 0 or fallback)
                values[i]
            };
        nums.push(val);
        i = i + 1;
    }

    let out_k: i32 =
        if mutation_kind == 8 {
            // k = 1
            1i32
        } else if mutation_kind == 9 {
            // k = nums.len()
            nums.len() as i32
        } else {
            k
        };

    (nums, out_k)
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

fn random_values(rng: &mut Rng, n: usize, val_lo: i64, val_hi: i64) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..n {
        v.push(rng.gen_range_i64(val_lo, val_hi) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1984);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($values:expr, $k:expr, $mk:expr) => {
            if count < goal {
                let values_val: Vec<i32> = $values;
                let k_val: i32 = $k;
                let mk_val: u8 = $mk;
                let (nums_out, k_out) = generate_test_case(&values_val, k_val, mk_val);
                let result = Solution::minimum_difference(nums_out.clone(), k_out);
                let line = json!({
                    "input": {"nums": nums_out, "k": k_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    // Example 1: nums = [90], k = 1 -> 0
    emit!(vec![90], 1, 0);
    // Example 2: nums = [9,4,1,7], k = 2 -> 2
    emit!(vec![9, 4, 1, 7], 2, 0);

    // ---- Boundary: single element, k=1 ----
    emit!(vec![0], 1, 0);
    emit!(vec![100_000], 1, 0);
    emit!(vec![50_000], 1, 0);

    // ---- Boundary: all same values ----
    for mk in 0u8..=9 {
        emit!(vec![42, 42, 42, 42], 2, mk);
    }

    // ---- Small arrays with all mutations ----
    for mk in 0u8..=9 {
        emit!(vec![1, 5, 3, 8, 2], 3, mk);
    }

    // ---- Boundary values in arrays ----
    emit!(vec![0, 0, 0, 0, 0], 3, 0);
    emit!(vec![100_000, 100_000, 100_000], 2, 0);
    emit!(vec![0, 100_000], 1, 0);
    emit!(vec![0, 100_000], 2, 0);

    // ---- k = 1 (always diff = 0) ----
    emit!(vec![10, 20, 30, 40, 50], 1, 0);

    // ---- k = n (full array) ----
    emit!(vec![10, 20, 30, 40, 50], 5, 0);

    // ---- Random tiny arrays (1-5 elements), all mutations ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(1, 5);
        let values = random_values(&mut rng, n, 0, 100_000);
        let k = rng.gen_range_usize(1, n) as i32;
        for mk in 0u8..=9 {
            emit!(values.clone(), k, mk);
        }
    }

    // ---- Random small arrays (6-20 elements) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(6, 20);
        let values = random_values(&mut rng, n, 0, 100_000);
        let k = rng.gen_range_usize(1, n) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit!(values.clone(), k, mk);
        emit!(values.clone(), k, 0);
    }

    // ---- Random medium arrays (21-200 elements) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(21, 200);
        let values = random_values(&mut rng, n, 0, 100_000);
        let k = rng.gen_range_usize(1, n) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit!(values.clone(), k, mk);
    }

    // ---- Random large arrays (201-1000 elements) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(201, 1000);
        let values = random_values(&mut rng, n, 0, 100_000);
        let k = rng.gen_range_usize(1, n) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit!(values.clone(), k, mk);
    }

    // ---- Maximum size (1000 elements) ----
    {
        let values = random_values(&mut rng, 1000, 0, 100_000);
        for mk in [0u8, 1, 2, 8, 9] {
            emit!(values.clone(), 500, mk);
        }
        emit!(values.clone(), 1, 0);
        emit!(values.clone(), 1000, 0);
    }

    // ---- Arrays with small value range (stress sliding window) ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(5, 50);
        let values = random_values(&mut rng, n, 0, 10);
        let k = rng.gen_range_usize(1, n) as i32;
        emit!(values.clone(), k, 0);
    }

    // ---- Arrays near boundaries with various k ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(2, 20);
        let values = random_values(&mut rng, n, 99_990, 100_000);
        let k = rng.gen_range_usize(1, n) as i32;
        emit!(values.clone(), k, 0);
    }

    // ---- Fill remaining with random sizes and random mutations ----
    while count < goal {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let values = random_values(&mut rng, n, 0, 100_000);
        let k = rng.gen_range_usize(1, n) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit!(values, k, mk);
    }
}
