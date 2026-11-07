use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value) +
                if s.last() == value { 1 as nat } else { 0 as nat }
        }
    }

    /// Identity pass-through; mutations are done in plain Rust in main().
    pub fn generate_test_case(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 30_000,
            forall |i: int| 0 <= i < nums.len() ==> -30_000 <= #[trigger] nums[i] <= 30_000,
            exists|unique_val: i32| {
                Self::count_occurrences(nums@, unique_val) == 1 &&
                forall|other: i32| other != unique_val ==>
                    Self::count_occurrences(nums@, other) % 2 == 0
            },
        ensures
            1 <= result.len() <= 30_000,
            forall |i: int| 0 <= i < result.len() ==> -30_000 <= #[trigger] result[i] <= 30_000,
            exists|unique_val: i32| {
                Self::count_occurrences(result@, unique_val) == 1 &&
                forall|other: i32| other != unique_val ==>
                    Self::count_occurrences(result@, other) % 2 == 0
            },
    {
        nums
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

include!("../code.rs");

/// Build a valid input: one unique value + n_pairs pairs, shuffled.
fn make_valid_input(rng: &mut Rng, unique: i32, pairs: &[i32]) -> Vec<i32> {
    let mut nums: Vec<i32> = Vec::with_capacity(1 + pairs.len() * 2);
    nums.push(unique);
    for &v in pairs {
        nums.push(v);
        nums.push(v);
    }
    // Fisher-Yates shuffle
    let n = nums.len();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        nums.swap(i, j);
    }
    nums
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

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::single_number(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 2, 1],
        vec![4, 1, 2, 1, 2],
        vec![1],
    ];
    for ex in examples {
        let result = Solution::generate_test_case(ex);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Edge cases: single element
    for &v in &[0i32, -30000, 30000, 1, -1] {
        let nums = vec![v];
        emit(nums, &mut seen, &mut out, &mut count);
    }

    // Small hand-crafted cases
    let hand_crafted: Vec<(i32, Vec<i32>)> = vec![
        (0, vec![1, 2, 3]),
        (30000, vec![-30000, 0, 1]),
        (-30000, vec![30000, 0, -1]),
        (7, vec![]),
        (42, vec![0, 1, -1, 100, -100]),
    ];
    for (unique, pairs) in hand_crafted {
        let nums = make_valid_input(&mut rng, unique, &pairs);
        let result = Solution::generate_test_case(nums);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Boundary: all same pairs + unique at boundary
    for &unique in &[-30000i32, 30000] {
        let pairs: Vec<i32> = (1..=10).collect();
        let nums = make_valid_input(&mut rng, unique, &pairs);
        let result = Solution::generate_test_case(nums);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Random inputs of various sizes with mutations
    let size_configs: Vec<(usize, usize)> = vec![
        (0, 0),   // size 1
        (0, 1),   // size 3
        (0, 4),   // size 9
        (1, 9),   // size 19
        (1, 49),  // size 99
        (1, 499), // size 999
        (1, 4999),// size 9999
        (1, 14999),// size 29999 (near max)
    ];

    while count < target {
        let cfg_idx = rng.gen_range_usize(0, size_configs.len() - 1);
        let (min_pairs, max_pairs) = size_configs[cfg_idx];
        let n_pairs = rng.gen_range_usize(min_pairs, max_pairs);
        let unique = rng.gen_range_i64(-30000, 30000) as i32;

        // Generate distinct pair values (distinct from unique)
        let mut pair_set: HashSet<i32> = HashSet::new();
        while pair_set.len() < n_pairs {
            let v = rng.gen_range_i64(-30000, 30000) as i32;
            if v != unique {
                pair_set.insert(v);
            }
        }
        let pairs: Vec<i32> = pair_set.into_iter().collect();
        let nums = make_valid_input(&mut rng, unique, &pairs);

        let result = Solution::generate_test_case(nums);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
