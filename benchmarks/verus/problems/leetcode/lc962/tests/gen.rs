use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 50_000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 50_000,
    ensures
        2 <= result.len() <= 50_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 50_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 0 (potential ramp end with small value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 50_000 (maximize ramp chance)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 50_000);
        d
    } else if mutation_kind == 3 {
        // set first element to 0 (maximize ramp chance from start)
        let mut d = nums;
        d.set(0, 0);
        d
    } else if mutation_kind == 4 {
        // set first element to 50_000 (minimize ramp chance from start)
        let mut d = nums;
        d.set(0, 50_000);
        d
    } else if mutation_kind == 5 {
        // set all elements to the same value (ramp width = n-1)
        let val = nums[0];
        let mut d = nums;
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 50_000,
                0 <= val <= 50_000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 6 && nums.len() < 50_000 {
        // grow by one element (push 0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 7 && nums.len() > 2 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 8 {
        // make strictly decreasing (no ramp exists, result should be 0)
        // set each element to 50_000 - i to create descending array
        let n = nums.len();
        let mut d = nums;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                d.len() == n,
                2 <= n <= 50_000,
                forall|j: int| 0 <= j < i ==> d[j] == 50_000 - j,
                forall|j: int| i <= j < n as int ==> d[j] == nums[j],
            decreases n - i,
        {
            d.set(i, (50_000 - i) as i32);
            i += 1;
        }
        d
    } else if mutation_kind == 9 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else {
        nums // fallback
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

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 50_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(962);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::max_width_ramp(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![6, 0, 8, 2, 1, 5],
        vec![9, 8, 1, 0, 1, 9, 4, 0, 4, 1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to example inputs
    for seed_nums in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(seed_nums.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Interesting seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![0, 0],                             // minimal, all same
        vec![50_000, 0],                         // decreasing pair
        vec![0, 50_000],                         // increasing pair
        vec![1, 2, 3, 4, 5],                    // sorted ascending
        vec![5, 4, 3, 2, 1],                    // sorted descending
        vec![0, 0, 0, 0, 0],                    // all zeros
        vec![50_000, 50_000, 50_000],            // all max
        vec![0, 50_000, 0, 50_000],              // alternating
        vec![10, 5, 10, 5, 10],                  // zigzag
    ];

    for seed_nums in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_nums.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),        // tiny
            1 => rng.gen_range_usize(2, 10),        // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 5000),    // big
        };
        let seed_nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
