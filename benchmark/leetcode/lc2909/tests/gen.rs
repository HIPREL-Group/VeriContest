use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000000,
    ensures
        3 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to min boundary (1)
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set last element to min boundary (1)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 3 {
        // set middle element to max boundary (100_000_000) — create a mountain peak
        let mut d = nums;
        let mid = d.len() / 2;
        d.set(mid, 100_000_000);
        d
    } else if mutation_kind == 4 && nums.len() < 100000 {
        // grow by one element (push 1)
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 5 && nums.len() > 3 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge first element: if < max, increment by 1
        let mut d = nums;
        if d[0] < 100_000_000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge last element: if > 1, decrement by 1
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 8 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 9 {
        // set all elements to 1 (no mountain triplet possible)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                3 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 10 {
        // create ascending sequence: set element at index mid to max boundary,
        // first to 1, last to 1 — guaranteed mountain
        let mut d = nums;
        let mid = d.len() / 2;
        d.set(0, 1);
        d.set(mid, 100_000_000);
        let last = d.len() - 1;
        d.set(last, 1);
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100_000_000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2909);
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
        let output = Solution::minimum_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<Vec<i32>> = vec![
        vec![8, 6, 1, 5, 3],
        vec![5, 4, 8, 7, 10, 2],
        vec![6, 5, 4, 3, 4, 5],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut emitted);
    }

    // Seed pool: hand-crafted interesting arrays
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1, 2, 1],                                 // minimal mountain
        vec![1, 1, 1],                                 // no mountain (all equal)
        vec![3, 2, 1],                                 // descending (no mountain)
        vec![1, 2, 3],                                 // ascending (no mountain)
        vec![1, 100_000_000, 1],                       // extreme peak
        vec![100_000_000, 1, 100_000_000],             // valley (no mountain)
        vec![1, 2, 1, 2, 1],                           // multiple mountains
        vec![50_000_000, 100_000_000, 50_000_000],     // large values mountain
    ];

    // Apply all mutation kinds to seed arrays
    let num_mutations: u8 = 11;
    for seed_arr in &seed_arrays {
        for mk in 0..num_mutations {
            if emitted >= count { break; }
            let mutated = mutate(seed_arr.clone(), mk);
            emit(mutated, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with diverse sizes and mutations
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(3, 5),        // tiny
            1 => rng.gen_range_usize(3, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let nums = random_nums(&mut rng, n);
        let mk = (rng.next_u64() % (num_mutations as u64 + 1)) as u8;
        let mutated = mutate(nums, mk);
        emit(mutated, &mut seen, &mut out, &mut emitted);
    }
}
