use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        1 <= k <= 100,
    ensures
        1 <= result.0.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        1 <= result.1 <= 100,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        (d, k)
    } else if mutation_kind == 2 {
        // set last element to 1000 (maximum value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1000);
        (d, k)
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 1000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 4 {
        // set all elements to 1000
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 1000,
                forall|j: int| 0 <= j < i ==> d[j] == 1000i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1000);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 5 && nums.len() < 1000 {
        // grow: append element with value 1
        let mut d = nums;
        d.push(1);
        (d, k)
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink: remove last element
        let mut d = nums;
        d.pop();
        (d, k)
    } else if mutation_kind == 7 {
        // nudge last element up (if < 1000)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 1000 {
            d.set(last, d[last] + 1);
        }
        (d, k)
    } else if mutation_kind == 8 {
        // nudge last element down (if > 1)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        (d, k)
    } else if mutation_kind == 9 && k < 100 {
        // nudge k up
        (nums, k + 1)
    } else if mutation_kind == 10 && k > 1 {
        // nudge k down
        (nums, k - 1)
    } else if mutation_kind == 11 {
        // set k to 1 (sum always divisible by 1)
        (nums, 1)
    } else if mutation_kind == 12 {
        // set k to 100 (max boundary)
        (nums, 100)
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1000) as i32);
    }
    v
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
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
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![3, 9, 7], 5),
        (vec![4, 1, 3], 4),
        (vec![3, 2], 6),
    ];
    for (nums, k) in &examples {
        emit(nums.clone(), *k, &mut seen, &mut out, &mut count);
    }

    // Seed arrays with diverse characteristics
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1],                          // single element, min value
        vec![1000],                       // single element, max value
        vec![500, 500],                   // two equal elements
        vec![1, 1, 1, 1, 1],             // all ones
        vec![1000, 1000, 1000],           // all max
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], // sequential
    ];

    let mutation_kinds: Vec<u8> = (0..=12).collect();
    let k_values: Vec<i32> = vec![1, 2, 3, 5, 7, 10, 50, 99, 100];

    // Apply mutations to seed arrays × k values
    for seed_arr in &seed_arrays {
        for &k in &k_values {
            for &mk in &mutation_kinds {
                let (result_nums, result_k) = generate_test_case(seed_arr.clone(), k, mk);
                emit(result_nums, result_k, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random seeds with random mutations across size classes
    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 500),   // large
            _ => rng.gen_range_usize(501, 1000),  // max
        };
        let nums = random_nums(&mut rng, len);
        let k = rng.gen_range_i64(1, 100) as i32;
        let mk = rng.gen_range_usize(0, 12) as u8;
        let (result_nums, result_k) = generate_test_case(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
