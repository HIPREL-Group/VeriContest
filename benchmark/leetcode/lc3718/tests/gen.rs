use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_vals: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= seed_vals.len() <= 100,
        forall|i: int| 0 <= i < seed_vals.len() ==> 1 <= #[trigger] seed_vals[i] <= 100,
        1 <= k <= 100,
    ensures
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 100,
{
    if mutation_kind == 0 {
        // identity
        (seed_vals, k)
    } else if mutation_kind == 1 && seed_vals.len() < 100 {
        // grow: push element 1
        let mut v = seed_vals;
        v.push(1);
        (v, k)
    } else if mutation_kind == 2 && seed_vals.len() > 1 {
        // shrink: pop last element
        let mut v = seed_vals;
        v.pop();
        (v, k)
    } else if mutation_kind == 3 {
        // set last element to 1 (boundary low)
        let mut v = seed_vals;
        let last = v.len() - 1;
        v.set(last, 1);
        (v, k)
    } else if mutation_kind == 4 {
        // set last element to 100 (boundary high)
        let mut v = seed_vals;
        let last = v.len() - 1;
        v.set(last, 100);
        (v, k)
    } else if mutation_kind == 5 {
        // set all elements to k (all same as k)
        let mut v = seed_vals;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == seed_vals.len(),
                1 <= v.len() <= 100,
                1 <= k <= 100,
                forall|j: int| 0 <= j < i ==> v[j] == k,
                forall|j: int| i <= j < v.len() ==> v[j] == seed_vals[j],
            decreases v.len() - i,
        {
            v.set(i, k);
            i += 1;
        }
        (v, k)
    } else if mutation_kind == 6 {
        // nudge last element up if < 100
        let mut v = seed_vals;
        let last = v.len() - 1;
        if v[last] < 100 {
            v.set(last, v[last] + 1);
        }
        (v, k)
    } else if mutation_kind == 7 {
        // nudge last element down if > 1
        let mut v = seed_vals;
        let last = v.len() - 1;
        if v[last] > 1 {
            v.set(last, v[last] - 1);
        }
        (v, k)
    } else if mutation_kind == 8 {
        // set first element to k
        let mut v = seed_vals;
        v.set(0, k);
        (v, k)
    } else if mutation_kind == 9 {
        // swap first and last elements
        let mut v = seed_vals;
        let last = v.len() - 1;
        let first_val = v[0];
        let last_val = v[last];
        v.set(0, last_val);
        v.set(last, first_val);
        (v, k)
    } else {
        // fallback: identity
        (seed_vals, k)
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3718);
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
        let output = Solution::missing_multiple(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![8, 2, 3, 4, 6], 2),
        (vec![1, 4, 7, 10, 15], 5),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // Seed arrays × mutation kinds
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100],
        vec![1, 2, 3, 4, 5],
        vec![50],
        vec![1, 1, 1],
        vec![10, 20, 30, 40, 50, 60, 70, 80, 90, 100],
        vec![2, 4, 6, 8, 10, 12, 14],
        vec![3, 6, 9, 12, 15],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![99, 100],
    ];
    let k_values: Vec<i32> = vec![1, 2, 3, 5, 7, 10, 50, 100];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for seed_arr in &seed_arrays {
        for &k in &k_values {
            for &mk in &mutation_kinds {
                let (nums, k_out) = generate_test_case(seed_arr.clone(), k, mk);
                emit(nums, k_out, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random inputs with diverse sizes and mutations
    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 30),     // medium
            3 => rng.gen_range_usize(31, 70),     // large
            _ => rng.gen_range_usize(71, 100),    // max
        };
        let k = rng.gen_range_i64(1, 100) as i32;
        let nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (result_nums, result_k) = generate_test_case(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
