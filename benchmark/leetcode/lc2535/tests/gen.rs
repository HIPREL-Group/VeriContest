use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 2000,
        forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 2000,
    ensures
        1 <= result.len() <= 2000,
        forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 2000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // nudge first element up
        let mut d = nums;
        if d[0] < 2000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 2 {
        // nudge first element down
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 3 {
        // set all elements to 1 (minimum boundary)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 2000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to 2000 (maximum boundary)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 2000,
                forall|j: int| 0 <= j < i ==> d[j] == 2000i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 2000);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && nums.len() < 2000 {
        // grow by one element (push 1)
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // set last element to boundary min (1)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 8 {
        // set last element to boundary max (2000)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 2000);
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 2000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2535);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::difference_of_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![1, 15, 6, 3],
        vec![1, 2, 3, 4],
    ];
    for seed_nums in &example_seeds {
        emit(seed_nums.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds for boundary coverage
    let crafted_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![2000],
        vec![1, 1],
        vec![2000, 2000],
        vec![10],
        vec![100],
        vec![1000],
        vec![999],
        vec![1999],
        vec![9, 9, 9],
        vec![10, 20, 30],
        vec![1, 2000],
        vec![100, 200, 300, 400, 500],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every crafted seed
    for seed_nums in &crafted_seeds {
        for &mk in &mutation_kinds {
            emit(mutate(seed_nums.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 500),     // large
            _ => rng.gen_range_usize(501, 2000),    // max
        };
        let seed_nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit(mutate(seed_nums, mk), &mut seen, &mut out, &mut count);
    }
}
