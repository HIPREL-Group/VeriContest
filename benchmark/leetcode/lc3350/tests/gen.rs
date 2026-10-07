use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 200_000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        2 <= result.len() <= 200_000,
        forall|i: int| 0 <= i < result.len() ==> -1_000_000_000 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut v = nums;
        v.set(0, 0);
        v
    } else if mutation_kind == 2 {
        // set first element to max boundary
        let mut v = nums;
        v.set(0, 1_000_000_000);
        v
    } else if mutation_kind == 3 {
        // set first element to min boundary
        let mut v = nums;
        v.set(0, -1_000_000_000);
        v
    } else if mutation_kind == 4 {
        // nudge first element up
        let mut v = nums;
        if v[0] < 1_000_000_000 {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 5 {
        // nudge first element down
        let mut v = nums;
        if v[0] > -1_000_000_000 {
            v.set(0, v[0] - 1);
        }
        v
    } else if mutation_kind == 6 && nums.len() < 200_000 {
        // grow by one element (push 0)
        let mut v = nums;
        v.push(0);
        v
    } else if mutation_kind == 7 && nums.len() > 2 {
        // shrink by one element (pop)
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 8 {
        // swap first two elements
        let mut v = nums;
        let tmp = v[0];
        v.set(0, v[1]);
        v.set(1, tmp);
        v
    } else if mutation_kind == 9 {
        // set all elements to 0
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                2 <= v.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> v[j] == 0i32,
                forall|j: int| i <= j < v.len() ==> #[trigger] v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 0);
            i += 1;
        }
        v
    } else if mutation_kind == 10 {
        // set last element to max boundary
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else if mutation_kind == 11 {
        // set last element to min boundary
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, -1_000_000_000);
        v
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

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize, val_lo: i64, val_hi: i64) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(val_lo, val_hi) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3350);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 5, 7, 8, 9, 2, 3, 4, 3, 1],
        vec![1, 2, 3, 4, 4, 4, 4, 5, 6, 7],
    ];

    for ex in &examples {
        let nums = ex.clone();
        let result = Solution::max_increasing_subarrays(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    // Apply mutations to examples
    for ex in &examples {
        for mk in 0u8..12 {
            if generated >= count { break; }
            let mutated = mutate(ex.clone(), mk);
            let result = Solution::max_increasing_subarrays(mutated.clone());
            writeln!(out, "{}", json!({"input": {"nums": mutated}, "output": result})).unwrap();
            generated += 1;
        }
    }

    // Random test cases across size classes
    while generated < count {
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(2, 5),          // tiny
            1 => rng.gen_range_usize(2, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 10_000),  // very large
        };

        // Mix value ranges for diversity
        let (val_lo, val_hi): (i64, i64) = match generated % 7 {
            0 => (-1_000_000_000, 1_000_000_000),  // full range
            1 => (0, 100),                          // small positive
            2 => (-100, 0),                         // small negative
            3 => (-10, 10),                         // very small
            4 => (1, 1_000_000_000),                // large positive
            5 => (-1_000_000_000, -1),              // large negative
            _ => (-1, 1),                           // around zero
        };

        let base_nums = random_nums(&mut rng, n, val_lo, val_hi);
        let mk = (rng.next_u64() % 12) as u8;
        let mutated = mutate(base_nums, mk);
        let result = Solution::max_increasing_subarrays(mutated.clone());
        writeln!(out, "{}", json!({"input": {"nums": mutated}, "output": result})).unwrap();
        generated += 1;
    }
}
