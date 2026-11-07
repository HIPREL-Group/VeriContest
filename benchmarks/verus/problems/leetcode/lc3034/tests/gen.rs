use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    pattern: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        2 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        1 <= pattern.len() <= 99,
        forall|i: int| 0 <= i < pattern.len() ==> -1 <= #[trigger] pattern[i] <= 1,
    ensures
        2 <= result.0.len() <= 100,
        1 <= result.1.len() < result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.1.len() ==> -1 <= #[trigger] result.1[i] <= 1,
{
    let mut n = nums;
    let mut pat = pattern;

    // Truncate pattern so that pat.len() < n.len()
    while pat.len() >= n.len()
        invariant
            1 <= pat.len(),
            2 <= n.len() <= 100,
            forall|i: int| 0 <= i < n.len() ==> 1 <= #[trigger] n[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < pat.len() ==> -1 <= #[trigger] pat[i] <= 1,
        decreases pat.len(),
    {
        pat.pop();
    }

    if mutation_kind == 0 {
        // identity
        (n, pat)
    } else if mutation_kind == 1 {
        // set pattern[0] to 1 (increasing)
        pat.set(0, 1);
        (n, pat)
    } else if mutation_kind == 2 {
        // set pattern[0] to -1 (decreasing)
        pat.set(0, -1);
        (n, pat)
    } else if mutation_kind == 3 {
        // set pattern[0] to 0 (equal)
        pat.set(0, 0);
        (n, pat)
    } else if mutation_kind == 4 && n[0] < 1_000_000_000 {
        // nudge nums[0] up
        n.set(0, n[0] + 1);
        (n, pat)
    } else if mutation_kind == 5 {
        // set nums[0] to min boundary
        n.set(0, 1);
        (n, pat)
    } else if mutation_kind == 6 && pat.len() > 1 {
        // shrink pattern by one
        pat.pop();
        (n, pat)
    } else if mutation_kind == 7 {
        // set nums[last] to max boundary
        let last = n.len() - 1;
        n.set(last, 1_000_000_000);
        (n, pat)
    } else if mutation_kind == 8 && n[0] > 1 {
        // nudge nums[0] down
        n.set(0, n[0] - 1);
        (n, pat)
    } else if mutation_kind == 9 && n.len() < 100 {
        // grow nums by one element
        n.push(1);
        (n, pat)
    } else {
        // fallback
        (n, pat)
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

fn mutate(nums: Vec<i32>, pattern: Vec<i32>, mutation_kind: u8) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(nums, pattern, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    v
}

fn random_pattern(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-1, 1) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, pattern: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}|{:?}", nums, pattern);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_matching_subarrays(nums.clone(), pattern.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "pattern": pattern},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 2, 3, 4, 5, 6], vec![1, 1]),
        (vec![1, 4, 4, 1, 3, 5, 5, 3], vec![1, 0, -1]),
    ];
    for (nums, pattern) in examples {
        emit(nums, pattern, &mut seen, &mut out, &mut count);
    }

    // Seed inputs with diverse structures
    let seed_inputs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 1], vec![0]),                           // min sizes, equal
        (vec![1, 2], vec![1]),                           // min sizes, increasing
        (vec![2, 1], vec![-1]),                          // min sizes, decreasing
        (vec![1, 1, 1, 1], vec![0, 0, 0]),               // all equal
        (vec![1, 2, 3, 4], vec![1, 1, 1]),               // all increasing
        (vec![4, 3, 2, 1], vec![-1, -1, -1]),             // all decreasing
        (vec![1, 2, 1, 2, 1], vec![1, -1]),               // alternating
        (vec![5, 5, 5, 5, 5, 5], vec![0]),                // all same, single pattern
        (vec![1_000_000_000, 1], vec![-1]),                // max value
        (vec![1, 1_000_000_000], vec![1]),                 // min to max
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed input
    for (nums, pattern) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (rn, rp) = mutate(nums.clone(), pattern.clone(), mk);
            emit(rn, rp, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with diverse size classes and mutations
    while count < target {
        // Size class for nums
        let n_len: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 3),    // tiny
            1 => rng.gen_range_usize(2, 10),   // small
            2 => rng.gen_range_usize(11, 50),  // medium
            3 => rng.gen_range_usize(51, 80),  // large
            _ => rng.gen_range_usize(81, 100), // max
        };

        // Pattern length: 1 to min(99, n_len - 1)
        let max_p = std::cmp::min(99, n_len - 1);
        let p_len: usize = if max_p <= 1 {
            1
        } else {
            match rng.gen_range_usize(0, 3) {
                0 => 1,                                  // single element
                1 => rng.gen_range_usize(1, max_p / 2 + 1), // short
                _ => rng.gen_range_usize(1, max_p),      // up to max
            }
        };

        let nums = random_nums(&mut rng, n_len);
        let pattern = random_pattern(&mut rng, p_len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (rn, rp) = mutate(nums, pattern, mk);
        emit(rn, rp, &mut seen, &mut out, &mut count);
    }
}
