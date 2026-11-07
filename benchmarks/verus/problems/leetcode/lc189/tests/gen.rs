use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: &mut Vec<i32>, k: i32, mutation_kind: u8)
    requires
        1 <= old(nums).len() <= 100_000,
        0 <= k <= 100_000,
    ensures
        1 <= old(nums).len() <= 100_000,
        0 <= k <= 100_000,
        1 <= nums.len() <= 100_000,
{
    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 && nums.len() < 100_000 {
        nums.push(0i32);
    } else if mutation_kind == 2 && nums.len() > 1 {
        nums.pop();
    } else if mutation_kind == 3 {
        let n = nums.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                nums.len() == n,
                1 <= n <= 100_000,
            decreases n - i,
        {
            nums.set(i, 0i32);
            i += 1;
        }
    } else if mutation_kind == 4 {
        if nums.len() >= 2 {
            let last = nums.len() - 1;
            let tmp = nums[0];
            nums.set(0, nums[last]);
            nums.set(last, tmp);
        }
    } else if mutation_kind == 5 {
        nums.set(0, i32::MIN);
    } else if mutation_kind == 6 {
        let last = nums.len() - 1;
        nums.set(last, i32::MAX);
    } else {
        // fallback: identity
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

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-2_147_483_648, 2_147_483_647) as i32);
    }
    v
}

fn mutate(nums: &mut Vec<i32>, k: i32, mutation_kind: u8) {
    generate_test_case(nums, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(189);
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
        let mut nums_clone = nums.clone();
        Solution::rotate(&mut nums_clone, k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": nums_clone})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1,2,3,4,5,6,7], 3),
        (vec![-1,-100,3,99], 2),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // Seed arrays with interesting patterns
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 2],
        vec![1, 2, 3],
        vec![0, 0, 0, 0],
        vec![i32::MIN, i32::MAX],
        vec![1, 2, 3, 4, 5],
        vec![-1, 0, 1],
        vec![42],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ];

    let k_values: Vec<i32> = vec![0, 1, 2, 3, 5, 7, 10, 100, 99999, 100000];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply seed arrays x k values x mutation kinds
    for arr in &seed_arrays {
        for &k in &k_values {
            for &mk in &mutation_kinds {
                let mut arr_mut = arr.clone();
                mutate(&mut arr_mut, k, mk);
                emit(arr_mut, k, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random test cases with size classes
    while count < target {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let mut arr = random_array(&mut rng, n);
        let k = rng.gen_range_i64(0, 100_000) as i32;
        let mk = rng.gen_range_usize(0, 7) as u8;
        mutate(&mut arr, k, mk);
        emit(arr, k, &mut seen, &mut out, &mut count);
    }
}
