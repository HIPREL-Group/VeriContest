use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
    ensures
        2 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> -100_000 <= #[trigger] result[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 0);
        v
    } else if mutation_kind == 2 {
        // set first element to 100_000 (max boundary)
        let mut v = nums;
        v.set(0, 100_000);
        v
    } else if mutation_kind == 3 {
        // set first element to -100_000 (min boundary)
        let mut v = nums;
        v.set(0, -100_000);
        v
    } else if mutation_kind == 4 {
        // nudge last element up (if < 100_000)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] < 100_000 {
            v.set(last, v[last] + 1);
        }
        v
    } else if mutation_kind == 5 {
        // nudge last element down (if > -100_000)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] > -100_000 {
            v.set(last, v[last] - 1);
        }
        v
    } else if mutation_kind == 6 {
        // negate first element (if in range)
        let mut v = nums;
        if v[0] > -100_000 && v[0] < 100_000 {
            v.set(0, -v[0]);
        }
        v
    } else if mutation_kind == 7 && nums.len() < 100_000 {
        // grow: append 0
        let mut v = nums;
        v.push(0);
        v
    } else if mutation_kind == 8 && nums.len() > 2 {
        // shrink: pop last element
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 9 {
        // set all elements to 0
        let n = nums.len();
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == n,
                2 <= v.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> v[j] == 0i32,
            decreases v.len() - i,
        {
            v.set(i, 0);
            i += 1;
        }
        v
    } else if mutation_kind == 10 && nums.len() >= 2 {
        // swap first and last elements
        let mut v = nums;
        let last = v.len() - 1;
        let tmp = v[0];
        v.set(0, v[last]);
        v.set(last, tmp);
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
        nums.push(rng.gen_range_i64(-100_000, 100_000) as i32);
    }
    nums
}

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
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::ways_to_split_array(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![10, 4, -8, 7],
        vec![2, 3, 1, 0],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut emitted);
    }

    // Seed pool with interesting arrays
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![0, 0],
        vec![100_000, -100_000],
        vec![-100_000, 100_000],
        vec![100_000, 100_000],
        vec![1, -1],
        vec![0, 0, 0, 0],
        vec![1, 2, 3, 4, 5],
        vec![-1, -2, -3, -4, -5],
    ];

    // Apply all mutation kinds to seed arrays
    let num_mutations: u8 = 11;
    for s in &seed_arrays {
        for mk in 0..num_mutations {
            if emitted >= count { break; }
            let mutated = mutate(s.clone(), mk);
            emit(mutated, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with diverse sizes
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(2, 5),         // tiny
            1 => rng.gen_range_usize(2, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // big
        };

        let nums = random_nums(&mut rng, n);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let mutated = mutate(nums, mk);
        emit(mutated, &mut seen, &mut out, &mut emitted);
    }
}
