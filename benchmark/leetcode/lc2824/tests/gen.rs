use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, target: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 50,
        -50 <= target <= 50,
        forall|k: int| 0 <= k < nums.len() ==> -50 <= #[trigger] nums[k] <= 50,
    ensures
        1 <= result.0.len() <= 50,
        -50 <= result.1 <= 50,
        forall|k: int| 0 <= k < result.0.len() ==> -50 <= #[trigger] result.0[k] <= 50,
{
    if mutation_kind == 0 {
        // identity
        (nums, target)
    } else if mutation_kind == 1 && target < 50 {
        // nudge target up
        (nums, target + 1)
    } else if mutation_kind == 2 && target > -50 {
        // nudge target down
        (nums, target - 1)
    } else if mutation_kind == 3 {
        // target = 0
        (nums, 0)
    } else if mutation_kind == 4 {
        // target = min boundary
        (nums, -50)
    } else if mutation_kind == 5 {
        // target = max boundary
        (nums, 50)
    } else if mutation_kind == 6 {
        // set all elements to 0
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        (d, target)
    } else if mutation_kind == 7 && nums.len() < 50 {
        // grow: push element 0
        let mut d = nums;
        d.push(0);
        (d, target)
    } else if mutation_kind == 8 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        (d, target)
    } else if mutation_kind == 9 {
        // set first element to -50
        let mut d = nums;
        d.set(0, -50);
        (d, target)
    } else if mutation_kind == 10 {
        // set first element to 50
        let mut d = nums;
        d.set(0, 50);
        (d, target)
    } else if mutation_kind == 11 {
        // set last element to -50
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, -50);
        (d, target)
    } else if mutation_kind == 12 {
        // set last element to 50
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 50);
        (d, target)
    } else if mutation_kind == 13 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        if last > 0 {
            d.set(last, first_val);
        }
        (d, target)
    } else if mutation_kind == 14 {
        // negate target (if in range)
        if target > -50 && target < 50 {
            (nums, -target)
        } else if target == -50 {
            (nums, 50)
        } else {
            // target == 50
            (nums, -50)
        }
    } else {
        // fallback: identity
        (nums, target)
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

fn mutate(nums: Vec<i32>, target: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(nums, target, mutation_kind)
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-50, 50) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2824);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, target: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", nums, target);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_pairs(nums.clone(), target);
        writeln!(out, "{}", json!({"input": {"nums": nums, "target": target}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![-1, 1, 2, 3, 1], 2),
        (vec![-6, 2, 5, -2, -7, -1, 3], -2),
    ];
    for (nums, tgt) in &examples {
        emit(nums.clone(), *tgt, &mut seen, &mut out, &mut count);
    }

    // Seed inputs: various shapes
    let seed_nums: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![-50],
        vec![50],
        vec![0, 0],
        vec![-50, 50],
        vec![50, -50],
        vec![1, 2, 3, 4, 5],
        vec![-1, -2, -3, -4, -5],
        vec![0, 0, 0, 0, 0],
        vec![-50, -50, -50],
        vec![50, 50, 50],
        vec![25, -25, 10, -10, 0],
    ];
    let seed_targets: Vec<i32> = vec![0, -50, 50, 1, -1, 2, -2, 25, -25];
    let mutation_kinds: Vec<u8> = (0..=14).collect();

    // Apply every mutation to seeds × targets
    for nums in &seed_nums {
        for &tgt in &seed_targets {
            for &mk in &mutation_kinds {
                let (result_nums, result_target) = mutate(nums.clone(), tgt, mk);
                emit(result_nums, result_target, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random inputs with random mutations
    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),   // tiny
            1 => rng.gen_range_usize(1, 10),  // small
            2 => rng.gen_range_usize(10, 25), // medium
            3 => rng.gen_range_usize(25, 40), // large
            _ => rng.gen_range_usize(40, 50), // max
        };
        let nums = random_nums(&mut rng, len);
        let tgt = rng.gen_range_i64(-50, 50) as i32;
        let mk = rng.gen_range_usize(0, 14) as u8;
        let (result_nums, result_target) = mutate(nums, tgt, mk);
        emit(result_nums, result_target, &mut seen, &mut out, &mut count);
    }
}
