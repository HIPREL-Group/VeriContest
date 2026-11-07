use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw_vals: Vec<i32>, mutation_kind: u8) -> (nums: Vec<i32>)
    requires
        1 <= raw_vals.len() <= 2500,
        forall|i: int| 0 <= i < raw_vals.len() ==> -10_000 <= (#[trigger] raw_vals[i]) <= 10_000,
    ensures
        1 <= nums.len() <= 2500,
        forall|i: int| 0 <= i < nums.len() ==> -10_000 <= (#[trigger] nums[i]) <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        raw_vals
    } else if mutation_kind == 1 {
        // set first element to -10_000 (boundary low)
        let mut v = raw_vals;
        v.set(0, -10_000i32);
        v
    } else if mutation_kind == 2 {
        // set last element to 10_000 (boundary high)
        let mut v = raw_vals;
        let last = v.len() - 1;
        v.set(last, 10_000i32);
        v
    } else if mutation_kind == 3 {
        // set all elements to 0 (constant array)
        let mut v = raw_vals;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == raw_vals.len(),
                1 <= v.len() <= 2500,
                forall|j: int| 0 <= j < i ==> v[j] == 0i32,
                forall|j: int| i <= j < v.len() ==> v[j] == raw_vals[j],
            decreases v.len() - i,
        {
            v.set(i, 0i32);
            i += 1;
        }
        v
    } else if mutation_kind == 4 && raw_vals.len() > 1 {
        // shrink by one (pop last element)
        let mut v = raw_vals;
        v.pop();
        v
    } else if mutation_kind == 5 && raw_vals.len() < 2500 {
        // grow by one (push 0)
        let mut v = raw_vals;
        v.push(0i32);
        v
    } else if mutation_kind == 6 {
        // nudge first element: clamp(val + 1, -10_000, 10_000)
        let mut v = raw_vals;
        let val = v[0];
        if val < 10_000 {
            v.set(0, val + 1);
        }
        v
    } else if mutation_kind == 7 {
        // nudge last element down: clamp(val - 1, -10_000, 10_000)
        let mut v = raw_vals;
        let last = v.len() - 1;
        let val = v[last];
        if val > -10_000 {
            v.set(last, val - 1);
        }
        v
    } else if mutation_kind == 8 {
        // negate first element
        let mut v = raw_vals;
        let val = v[0];
        v.set(0, -val);
        v
    } else if mutation_kind == 9 && raw_vals.len() >= 2 {
        // swap first and last elements
        let mut v = raw_vals;
        let last = v.len() - 1;
        let first_val = v[0];
        let last_val = v[last];
        v.set(0, last_val);
        v.set(last, first_val);
        v
    } else {
        // fallback: identity
        raw_vals
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

fn mutate(raw_vals: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(raw_vals, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-10_000, 10_000) as i32);
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

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::length_of_lis(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<Vec<i32>> = vec![
        vec![10, 9, 2, 5, 3, 7, 101, 18],
        vec![0, 1, 0, 3, 2, 3],
        vec![7, 7, 7, 7, 7, 7, 7],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every example
    for seed_input in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(seed_input.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Boundary seeds
    let boundary_seeds: Vec<Vec<i32>> = vec![
        vec![0],                        // single element 0
        vec![-10_000],                  // single element min
        vec![10_000],                   // single element max
        vec![1, 2, 3, 4, 5],           // strictly increasing
        vec![5, 4, 3, 2, 1],           // strictly decreasing
        vec![0; 10],                    // all same
    ];

    for seed_input in &boundary_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_input.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with size classes and random mutations
    while count < target {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 500),     // large
            _ => rng.gen_range_usize(501, 2500),    // max
        };
        let seed_input = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_input, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
