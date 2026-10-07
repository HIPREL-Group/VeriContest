use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 100000,
        0 <= k < nums.len(),
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1_073_741_824,
    ensures
        1 <= result.0.len() <= 100000,
        0 <= result.1 < result.0.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] < 1_073_741_824,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut n = nums;
        n.set(0, 0);
        (n, k)
    } else if mutation_kind == 2 {
        // set first element to max
        let mut n = nums;
        n.set(0, 1_073_741_823);
        (n, k)
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut n = nums;
        let last = n.len() - 1;
        n.set(last, 0);
        (n, k)
    } else if mutation_kind == 4 {
        // set last element to max
        let mut n = nums;
        let last = n.len() - 1;
        n.set(last, 1_073_741_823);
        (n, k)
    } else if mutation_kind == 5 {
        // set all elements to 0
        let mut n = nums;
        let len = n.len();
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == len,
                1 <= len <= 100000,
                0 <= k < len,
                forall |j: int| 0 <= j < n.len() ==> 0 <= #[trigger] n[j] < 1_073_741_824,
            decreases n.len() - i,
        {
            n.set(i, 0);
            i += 1;
        }
        (n, k)
    } else if mutation_kind == 6 {
        // set all elements to max
        let mut n = nums;
        let len = n.len();
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == len,
                1 <= len <= 100000,
                0 <= k < len,
                forall |j: int| 0 <= j < n.len() ==> 0 <= #[trigger] n[j] < 1_073_741_824,
            decreases n.len() - i,
        {
            n.set(i, 1_073_741_823);
            i += 1;
        }
        (n, k)
    } else if mutation_kind == 7 {
        // set k to 0
        (nums, 0i32)
    } else if mutation_kind == 8 {
        // set k to len - 1
        let new_k = (nums.len() - 1) as i32;
        (nums, new_k)
    } else if mutation_kind == 9 {
        // nudge first element up (if possible)
        let mut n = nums;
        let v = n[0];
        if v < 1_073_741_823 {
            n.set(0, v + 1);
        }
        (n, k)
    } else if mutation_kind == 10 {
        // nudge first element down (if possible)
        let mut n = nums;
        let v = n[0];
        if v > 0 {
            n.set(0, v - 1);
        }
        (n, k)
    } else if mutation_kind == 11 {
        // halve first element
        let mut n = nums;
        let v = n[0];
        n.set(0, v / 2);
        (n, k)
    } else {
        // fallback identity
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
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 1_073_741_823) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3022);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_or_after_operations(nums.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "k": k},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![3, 5, 3, 2, 7], 2),
        (vec![7, 3, 15, 14, 2, 8], 4),
        (vec![10, 7, 10, 3, 9, 14, 9, 4], 1),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut total);
    }

    // Mutation kinds
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Seed arrays with diverse sizes and values, apply all mutations
    let seed_configs: Vec<(usize, i64, i64)> = vec![
        (1, 0, 0),                         // single element, zero
        (1, 1_073_741_823, 1_073_741_823), // single element, max
        (2, 0, 100),                       // tiny
        (5, 0, 1_073_741_823),             // small, full range
        (10, 0, 255),                      // small, byte range
        (50, 0, 1_073_741_823),            // medium
        (100, 0, 1023),                    // medium, 10-bit values
    ];

    for &(len, lo, hi) in &seed_configs {
        let nums: Vec<i32> = (0..len).map(|_| rng.gen_range_i64(lo, hi) as i32).collect();
        let k = rng.gen_range_usize(0, len - 1) as i32;
        for &mk in &mutation_kinds {
            let (result_nums, result_k) = generate_test_case(nums.clone(), k, mk);
            emit(result_nums, result_k, &mut seen, &mut out, &mut total);
        }
    }

    // Random test cases with diverse size classes
    while total < count {
        let len = match total % 5 {
            0 => rng.gen_range_usize(1, 5),          // tiny
            1 => rng.gen_range_usize(1, 20),         // small
            2 => rng.gen_range_usize(21, 200),       // medium
            3 => rng.gen_range_usize(201, 2000),     // large
            _ => rng.gen_range_usize(2001, 10000),   // very large
        };

        // Mix value ranges
        let (lo, hi) = match total % 4 {
            0 => (0i64, 1_073_741_823i64),           // full range
            1 => (0i64, 1i64),                       // binary values
            2 => (0i64, 255i64),                     // byte range
            _ => (1_073_741_800i64, 1_073_741_823i64), // near max
        };

        let nums = random_nums(&mut rng, len);
        let k = rng.gen_range_usize(0, len - 1) as i32;
        let mk = rng.gen_range_usize(0, 11) as u8;

        // Override some values based on value range selection
        let nums: Vec<i32> = nums.iter().map(|_| rng.gen_range_i64(lo, hi) as i32).collect();

        let (result_nums, result_k) = generate_test_case(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut total);
    }
}
