use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 10_000,
        forall|i: int| 0 <= i < result.len() ==> -1_000_000_000 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set all elements to same value (LCIS = 1)
        let val = nums[0];
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 10_000,
                -1_000_000_000 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> #[trigger] d[j] == val,
                forall|j: int| i <= j < d.len() ==> -1_000_000_000 <= #[trigger] d[j] <= 1_000_000_000,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 2 {
        // nudge first element up (if possible)
        let mut d = nums;
        if d[0] < 1_000_000_000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 3 {
        // nudge first element down (if possible)
        let mut d = nums;
        if d[0] > -1_000_000_000 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 4 {
        // nudge last element up (if possible)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 1_000_000_000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 5 {
        // nudge last element down (if possible)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > -1_000_000_000 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 6 && nums.len() < 10_000 {
        // grow: push 0
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 7 && nums.len() > 1 {
        // shrink: pop last
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 8 {
        // set last element to min boundary
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, -1_000_000_000);
        d
    } else if mutation_kind == 9 {
        // set last element to max boundary
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1_000_000_000);
        d
    } else if mutation_kind == 10 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0);
        d
    } else if mutation_kind == 11 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else {
        // fallback: identity
        nums
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo, hi) as i32);
    }
    v
}

fn make_increasing(base: i32, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        v.push(base + i as i32);
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::find_length_of_lcis(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 3, 5, 4, 7],
        vec![2, 2, 2, 2, 2],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Emit examples with all mutations
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Hand-crafted seeds: edge cases for LCIS
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],                                        // single element
        vec![1, 2],                                     // two increasing
        vec![2, 1],                                     // two decreasing
        vec![1, 2, 3, 4, 5],                            // all increasing
        vec![5, 4, 3, 2, 1],                            // all decreasing
        vec![1, 3, 5, 7, 2, 4, 6, 8],                   // two runs
        vec![1_000_000_000],                             // max boundary
        vec![-1_000_000_000],                            // min boundary
        vec![-1_000_000_000, 1_000_000_000],             // min to max
        vec![0, 0, 0, 1, 2, 3, 0, 0],                   // run in middle
        make_increasing(-5, 11),                         // consecutive -5..5
        make_increasing(0, 100),                         // medium increasing
    ];

    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Random inputs across size classes
    while total < count {
        let n: usize = match total % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // max
        };

        // Vary value ranges
        let (lo, hi): (i64, i64) = match total % 4 {
            0 => (-1_000_000_000, 1_000_000_000),   // full range
            1 => (-10, 10),                          // small range (many ties)
            2 => (0, 100),                           // non-negative small
            _ => (-1_000_000, 1_000_000),            // moderate range
        };

        let nums = random_nums(&mut rng, n, lo, hi);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = mutate(nums, mk);
        emit(result, &mut seen, &mut out, &mut total);
    }
}
