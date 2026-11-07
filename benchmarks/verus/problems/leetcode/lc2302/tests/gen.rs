use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i64, mutation_kind: u8) -> (result: (Vec<i32>, i64))
    requires
        1 <= nums.len() <= 100_000,
        1 <= k <= 1_000_000_000_000_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1 <= 1_000_000_000_000_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set first element to 1 (min value)
        let mut n = nums;
        n.set(0, 1);
        (n, k)
    } else if mutation_kind == 2 {
        // set first element to 100_000 (max value)
        let mut n = nums;
        n.set(0, 100_000);
        (n, k)
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == nums.len(),
                1 <= n.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> n[j] == 1i32,
                forall|j: int| i <= j < n.len() ==> n[j] == nums[j],
            decreases n.len() - i,
        {
            n.set(i, 1);
            i += 1;
        }
        (n, k)
    } else if mutation_kind == 4 {
        // set all elements to 100_000
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == nums.len(),
                1 <= n.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> n[j] == 100_000i32,
                forall|j: int| i <= j < n.len() ==> n[j] == nums[j],
            decreases n.len() - i,
        {
            n.set(i, 100_000);
            i += 1;
        }
        (n, k)
    } else if mutation_kind == 5 && nums.len() < 100_000 {
        // grow by one element (push 1)
        let mut n = nums;
        n.push(1);
        (n, k)
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut n = nums;
        n.pop();
        (n, k)
    } else if mutation_kind == 7 {
        // set last element to 1
        let mut n = nums;
        let last = n.len() - 1;
        n.set(last, 1);
        (n, k)
    } else if mutation_kind == 8 {
        // set last element to 100_000
        let mut n = nums;
        let last = n.len() - 1;
        n.set(last, 100_000);
        (n, k)
    } else if mutation_kind == 9 {
        // set k to 1 (minimum k)
        (nums, 1i64)
    } else if mutation_kind == 10 {
        // set k to max
        (nums, 1_000_000_000_000_000i64)
    } else if mutation_kind == 11 && nums.len() >= 2 {
        // swap first and last elements
        let mut n = nums;
        let last = n.len() - 1;
        let first_val = n[0];
        let last_val = n[last];
        n.set(0, last_val);
        n.set(last, first_val);
        (n, k)
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
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn mutate(nums: Vec<i32>, k: i64, mutation_kind: u8) -> (Vec<i32>, i64) {
    generate_test_case(nums, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    nums
}

fn random_k(rng: &mut Rng) -> i64 {
    rng.gen_range_i64(1, 1_000_000_000_000_000)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2302);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) { return; }
        let result = Solution::count_subarrays(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": result})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i64)> = vec![
        (vec![2, 1, 4, 3, 5], 10),
        (vec![1, 1, 1], 5),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // Seed inputs with various sizes and values
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100_000],
        vec![1, 1],
        vec![100_000, 100_000],
        vec![1, 2, 3, 4, 5],
        vec![50_000, 50_000, 50_000],
        vec![1, 100_000],
        vec![99_999, 100_000, 1],
    ];
    let seed_ks: Vec<i64> = vec![1, 2, 10, 100, 1_000_000, 1_000_000_000_000_000];
    let mutation_kinds: Vec<u8> = (0..=11).collect();

    for arr in &seed_arrays {
        for &k in &seed_ks {
            for &mk in &mutation_kinds {
                let (result_nums, result_k) = mutate(arr.clone(), k, mk);
                emit(result_nums, result_k, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random inputs across size classes
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 5000),  // very large
        };
        let nums = random_nums(&mut rng, len);
        let k = random_k(&mut rng);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (result_nums, result_k) = mutate(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
