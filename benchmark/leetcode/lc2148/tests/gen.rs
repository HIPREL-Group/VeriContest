use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
    ensures
        result.len() <= 2147483647usize,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() < 100 {
        // grow: push 0
        let mut v = nums;
        v.push(0i32);
        v
    } else if mutation_kind == 2 && nums.len() > 1 {
        // shrink: pop last element
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 3 {
        // set all elements to the same value (no strictly smaller/greater)
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                v.len() <= 100,
            decreases v.len() - i,
        {
            v.set(i, 0i32);
            i += 1;
        }
        v
    } else if mutation_kind == 4 {
        // nudge first element up by 1
        let mut v = nums;
        if v[0] < 100_000 {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 5 {
        // nudge first element down by 1
        let mut v = nums;
        if v[0] > -100_000 {
            v.set(0, v[0] - 1);
        }
        v
    } else if mutation_kind == 6 && nums.len() >= 2 {
        // swap first and last elements
        let mut v = nums;
        let last = v.len() - 1;
        let tmp = v[0];
        v.set(0, v[last]);
        v.set(last, tmp);
        v
    } else if mutation_kind == 7 {
        // set first element to min boundary
        let mut v = nums;
        v.set(0, -100_000i32);
        v
    } else if mutation_kind == 8 {
        // set first element to max boundary
        let mut v = nums;
        v.set(0, 100_000i32);
        v
    } else if mutation_kind == 9 {
        // negate first element
        let mut v = nums;
        if v[0] > -100_000 {
            v.set(0, -v[0]);
        }
        v
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-100_000, 100_000) as i32);
    }
    v
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2148);
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
        let output = Solution::count_elements(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<Vec<i32>> = vec![
        vec![11, 7, 2, 15],
        vec![-3, 3, 3, 90],
    ];

    let mutation_kinds: Vec<u8> = (0..=9).collect();

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Interesting seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 2],
        vec![5, 5, 5],
        vec![1, 2, 3, 4, 5],
        vec![-100_000, 100_000],
        vec![0, 0, 0, 0],
        vec![-1, 0, 1],
        vec![100_000, -100_000, 0, 50_000, -50_000],
        vec![1, 1, 1, 1, 2],
        vec![1, 2, 1, 2, 1],
    ];

    for seed in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(seed.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with random mutations across size classes
    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),    // tiny
            1 => rng.gen_range_usize(1, 10),   // small
            2 => rng.gen_range_usize(11, 50),  // medium
            3 => rng.gen_range_usize(51, 100), // large
            _ => rng.gen_range_usize(1, 100),  // fallback
        };
        let nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }
}
