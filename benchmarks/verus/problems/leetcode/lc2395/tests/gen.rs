use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        2 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> -1_000_000_000 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 3 {
        // set all elements to 0 (forces equal sums if len >= 3)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 1000,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums[0] < 1_000_000_000i32 {
        // nudge first element up
        let mut d = nums;
        d.set(0, d[0] + 1);
        d
    } else if mutation_kind == 5 && nums[0] > -1_000_000_000i32 {
        // nudge first element down
        let mut d = nums;
        d.set(0, d[0] - 1);
        d
    } else if mutation_kind == 6 && nums.len() < 1000 {
        // grow: append 0
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 7 && nums.len() > 2 {
        // shrink: remove last
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 8 {
        // set first element to max boundary
        let mut d = nums;
        d.set(0, 1_000_000_000i32);
        d
    } else if mutation_kind == 9 {
        // set first element to min boundary
        let mut d = nums;
        d.set(0, -1_000_000_000i32);
        d
    } else if mutation_kind == 10 && nums.len() >= 3 {
        // make nums[0]+nums[1] == nums[1]+nums[2] by setting nums[2] = nums[0]
        let mut d = nums;
        let v = d[0];
        d.set(2, v);
        d
    } else if mutation_kind == 11 {
        // negate first element
        let mut d = nums;
        let v = d[0];
        if v > -1_000_000_000i32 {
            d.set(0, -v);
        }
        d
    } else if mutation_kind == 12 && nums.len() >= 2 {
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

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize, val_lo: i64, val_hi: i64) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(val_lo, val_hi) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2395);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::find_subarrays(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![4, 2, 4],
        vec![1, 2, 3, 4, 5],
        vec![0, 0, 0],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut emitted);
    }

    // Boundary / special seeds
    let special_seeds: Vec<Vec<i32>> = vec![
        vec![0, 0],
        vec![1_000_000_000, -1_000_000_000],
        vec![-1_000_000_000, 1_000_000_000],
        vec![1_000_000_000, 1_000_000_000],
        vec![-1_000_000_000, -1_000_000_000],
        vec![0, 1, 0],
        vec![1, 1, 1],
        vec![-1, -1, -1],
        vec![1, 2, 1, 2],
        vec![5, 5, 5, 5, 5],
    ];
    for s in &special_seeds {
        for mk in 0..=12u8 {
            let mutated = mutate(s.clone(), mk);
            emit(mutated, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with diverse sizes and mutations
    let num_mutations = 13u8;
    while emitted < count {
        // Size classes
        let n = match emitted % 5 {
            0 => rng.gen_range_usize(2, 3),        // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };

        // Value range diversity
        let (val_lo, val_hi): (i64, i64) = match emitted % 4 {
            0 => (-1_000_000_000, 1_000_000_000),  // full range
            1 => (-100, 100),                       // small values
            2 => (0, 1_000_000_000),                // non-negative
            _ => (-1_000_000_000, 0),               // non-positive
        };

        let base = random_nums(&mut rng, n, val_lo, val_hi);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let mutated = mutate(base, mk);
        emit(mutated, &mut seen, &mut out, &mut emitted);
    }
}
