use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        2 <= nums.len() <= 100000,
        nums.len() % 2 == 0,
        0 <= k <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= k,
    ensures
        2 <= result.0.len() <= 100000,
        result.0.len() % 2 == 0,
        0 <= result.1 <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= result.1,
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
        // set first element to k
        let mut d = nums;
        d.set(0, k);
        (d, k)
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        (d, k)
    } else if mutation_kind == 4 {
        // set last element to k
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, k);
        (d, k)
    } else if mutation_kind == 5 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let tmp = d[0];
        d.set(0, d[last]);
        d.set(last, tmp);
        (d, k)
    } else if mutation_kind == 6 && nums[0] < k {
        // nudge first element up
        let mut d = nums;
        d.set(0, d[0] + 1);
        (d, k)
    } else if mutation_kind == 7 && nums[0] > 0 {
        // nudge first element down
        let mut d = nums;
        d.set(0, d[0] - 1);
        (d, k)
    } else if mutation_kind == 8 && nums.len() <= 99998 {
        // grow by 2 elements (push 0, 0)
        let mut d = nums;
        d.push(0);
        d.push(0);
        (d, k)
    } else if mutation_kind == 9 && nums.len() > 2 {
        // shrink by 2 elements (pop twice)
        let mut d = nums;
        d.pop();
        d.pop();
        (d, k)
    } else if mutation_kind == 10 {
        // set all elements to 0
        let n = nums.len();
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                2 <= d.len() <= 100000,
                d.len() % 2 == 0,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                0 <= k <= 100000,
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 11 {
        // set all elements to k
        let n = nums.len();
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                2 <= d.len() <= 100000,
                d.len() % 2 == 0,
                forall|j: int| 0 <= j < i ==> d[j] == k,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                0 <= k <= 100000,
            decreases d.len() - i,
        {
            d.set(i, k);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 12 && k > 0 {
        // decrease k to k-1, clamp elements
        let new_k = k - 1;
        let n = nums.len();
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                2 <= d.len() <= 100000,
                d.len() % 2 == 0,
                0 <= new_k <= 100000,
                new_k == k - 1,
                forall|j: int| 0 <= j < i ==> 0 <= #[trigger] d[j] <= new_k,
                forall|j: int| i <= j < d.len() ==> 0 <= #[trigger] d[j] <= k,
            decreases d.len() - i,
        {
            if d[i] > new_k {
                d.set(i, new_k);
            }
            i += 1;
        }
        (d, new_k)
    } else if mutation_kind == 13 && k < 100000 {
        // increase k by 1
        (nums, k + 1)
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

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize, k: i32) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, k as i64) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3224);
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
        let output = Solution::min_changes(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    emit(vec![1, 0, 1, 2, 4, 3], 4, &mut seen, &mut out, &mut count);
    emit(vec![0, 1, 2, 3, 3, 6, 5, 4], 6, &mut seen, &mut out, &mut count);

    // Seed inputs: various sizes and k values
    let seed_configs: Vec<(usize, i32)> = vec![
        (2, 0),        // minimum length, k=0
        (2, 1),        // minimum length, k=1
        (2, 100000),   // minimum length, max k
        (4, 5),        // small
        (6, 10),       // small
        (10, 100),     // medium-small
        (20, 1000),    // medium
        (100, 10000),  // medium-large
        (1000, 100000),// large
        (10000, 100000),// very large
        (4, 0),        // all zeros forced
    ];

    let mutation_kinds: Vec<u8> = (0..=13).collect();

    // Apply every mutation to every seed config
    for &(n, k) in &seed_configs {
        let nums = random_nums(&mut rng, n, k);
        for &mk in &mutation_kinds {
            let (result_nums, result_k) = generate_test_case(nums.clone(), k, mk);
            emit(result_nums, result_k, &mut seen, &mut out, &mut count);
        }
    }

    // Size classes for random generation
    while count < target {
        let n_half = match count % 5 {
            0 => rng.gen_range_usize(1, 3),          // tiny: 2-6
            1 => rng.gen_range_usize(2, 10),         // small: 4-20
            2 => rng.gen_range_usize(10, 50),        // medium: 20-100
            3 => rng.gen_range_usize(50, 500),       // large: 100-1000
            _ => rng.gen_range_usize(500, 5000),     // very large: 1000-10000
        };
        let n = n_half * 2;
        let k = match count % 4 {
            0 => 0,
            1 => rng.gen_range_i64(1, 100) as i32,
            2 => rng.gen_range_i64(100, 10000) as i32,
            _ => rng.gen_range_i64(10000, 100000) as i32,
        };
        let nums = random_nums(&mut rng, n, k);
        let mk = rng.gen_range_usize(0, 13) as u8;
        let (result_nums, result_k) = generate_test_case(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
