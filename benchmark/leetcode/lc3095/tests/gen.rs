use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 50,
        0 <= k < 64,
    ensures
        1 <= result.0.len() <= 50,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 50,
        0 <= result.1 < 64,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0);
        (d, k)
    } else if mutation_kind == 2 {
        // set first element to 50 (max value)
        let mut d = nums;
        d.set(0, 50);
        (d, k)
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 4 {
        // set all elements to 50
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 50i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 50);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 5 && nums.len() < 50 {
        // grow: append element 0
        let mut d = nums;
        d.push(0);
        (d, k)
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink: remove last element
        let mut d = nums;
        d.pop();
        (d, k)
    } else if mutation_kind == 7 {
        // nudge last element up (if < 50)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 50 {
            d.set(last, d[last] + 1);
        }
        (d, k)
    } else if mutation_kind == 8 {
        // nudge last element down (if > 0)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 0 {
            d.set(last, d[last] - 1);
        }
        (d, k)
    } else if mutation_kind == 9 {
        // mutate k: set to 0
        (nums, 0)
    } else if mutation_kind == 10 {
        // mutate k: set to 63 (max)
        (nums, 63)
    } else if mutation_kind == 11 && k < 63 {
        // mutate k: nudge up
        (nums, k + 1)
    } else if mutation_kind == 12 && k > 0 {
        // mutate k: nudge down
        (nums, k - 1)
    } else if mutation_kind == 13 {
        // swap first and last elements
        if nums.len() > 1 {
            let mut d = nums;
            let last = d.len() - 1;
            let tmp = d[0];
            d.set(0, d[last]);
            d.set(last, tmp);
            (d, k)
        } else {
            (nums, k)
        }
    } else {
        // fallback: identity
        (nums, k)
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

fn mutate(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(nums, k, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 50) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3095);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::minimum_subarray_length(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 2, 3], 2),
        (vec![2, 1, 8], 10),
        (vec![1, 2], 0),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // Seed arrays with interesting patterns
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![0],
        vec![50],
        vec![0, 0, 0],
        vec![50, 50, 50],
        vec![1],
        vec![0, 0],
        vec![1, 2, 4, 8, 16, 32],
        vec![7, 7, 7, 7, 7],
        vec![48, 3],
        vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ];
    let seed_ks: Vec<i32> = vec![0, 1, 7, 15, 31, 50, 63];
    let mutation_kinds: Vec<u8> = (0..=13).collect();

    // Cross-product: seeds × k values × mutations
    for seed_arr in &seed_arrays {
        for &k in &seed_ks {
            for &mk in &mutation_kinds {
                let (result_nums, result_k) = mutate(seed_arr.clone(), k, mk);
                emit(result_nums, result_k, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random inputs with random mutations
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 25),     // medium
            3 => rng.gen_range_usize(26, 40),     // large
            _ => rng.gen_range_usize(41, 50),     // max
        };
        let nums = random_nums(&mut rng, len);
        let k = rng.gen_range_i64(0, 63) as i32;
        let mk = rng.gen_range_usize(0, 13) as u8;
        let (result_nums, result_k) = mutate(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
