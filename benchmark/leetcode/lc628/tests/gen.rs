use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        nums.len() >= 3,
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
    ensures
        result.len() >= 3,
        forall|i: int| 0 <= i < result.len() ==> -1000 <= #[trigger] result[i] <= 1000,
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
        // set first element to -1000 (min boundary)
        let mut d = nums;
        d.set(0, -1000);
        d
    } else if mutation_kind == 3 {
        // set first element to 1000 (max boundary)
        let mut d = nums;
        d.set(0, 1000);
        d
    } else if mutation_kind == 4 {
        // negate first element
        let mut d = nums;
        let v = d[0];
        if v > -1000 {
            d.set(0, -v);
        }
        d
    } else if mutation_kind == 5 {
        // set all elements to 0
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                d.len() >= 3,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // set all elements to -1000
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                d.len() >= 3,
                forall|j: int| 0 <= j < i ==> d[j] == -1000i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, -1000);
            i += 1;
        }
        d
    } else if mutation_kind == 7 {
        // set all elements to 1000
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                d.len() >= 3,
                forall|j: int| 0 <= j < i ==> d[j] == 1000i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1000);
            i += 1;
        }
        d
    } else if mutation_kind == 8 && nums.len() < 10000 {
        // grow: push one element (0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 9 && nums.len() > 3 {
        // shrink: pop one element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 10 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 11 {
        // nudge first element up (if < 1000)
        let mut d = nums;
        if d[0] < 1000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 12 {
        // nudge first element down (if > -1000)
        let mut d = nums;
        if d[0] > -1000 {
            d.set(0, d[0] - 1);
        }
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(628);
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
        let output = Solution::maximum_product(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3],
        vec![1, 2, 3, 4],
        vec![-1, -2, -3],
    ];

    let mutation_kinds: Vec<u8> = (0..=12).collect();

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Curated seeds: boundary and interesting cases
    let curated: Vec<Vec<i32>> = vec![
        vec![0, 0, 0],
        vec![-1000, -1000, -1000],
        vec![1000, 1000, 1000],
        vec![-1000, -999, 1000],
        vec![-1000, 999, 1000],
        vec![-1, 0, 1],
        vec![-1000, -1000, 1000, 1000],
        vec![0, 0, 0, 0, 0],
        vec![1, 1, 1, 1, 1],
        vec![-1, -1, -1, -1, -1],
        vec![-1000, 0, 1000],
        vec![500, 500, 500],
    ];

    for seed_arr in &curated {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    while count < target {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(3, 5),      // tiny
            1 => rng.gen_range_usize(3, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // very large
        };
        let seed_arr = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 12) as u8;
        let result = mutate(seed_arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
