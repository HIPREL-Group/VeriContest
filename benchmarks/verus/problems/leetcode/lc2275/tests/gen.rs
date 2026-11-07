use vstd::prelude::*;

verus! {

pub fn generate_test_case(candidates: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= candidates.len() <= 100000,
        forall|i: int| 0 <= i < candidates.len() ==> 1 <= #[trigger] candidates[i] <= 10_000_000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10_000_000,
{
    if mutation_kind == 0 {
        // identity
        candidates
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut c = candidates;
        let last = c.len() - 1;
        c.set(last, 1);
        c
    } else if mutation_kind == 2 {
        // set last element to 10_000_000 (max boundary)
        let mut c = candidates;
        let last = c.len() - 1;
        c.set(last, 10_000_000);
        c
    } else if mutation_kind == 3 {
        // set all elements to the same value (first element)
        let val = candidates[0];
        let mut c = candidates;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == candidates.len(),
                1 <= c.len() <= 100000,
                1 <= val <= 10_000_000,
                forall|j: int| 0 <= j < i ==> c[j] == val,
                forall|j: int| i <= j < c.len() ==> c[j] == candidates[j],
            decreases c.len() - i,
        {
            c.set(i, val);
            i += 1;
        }
        c
    } else if mutation_kind == 4 && candidates.len() < 100000 {
        // grow by one: push first element
        let val = candidates[0];
        let mut c = candidates;
        c.push(val);
        c
    } else if mutation_kind == 5 && candidates.len() > 1 {
        // shrink by one: pop last element
        let mut c = candidates;
        c.pop();
        c
    } else if mutation_kind == 6 {
        // nudge first element up (if below max)
        let mut c = candidates;
        if c[0] < 10_000_000 {
            c.set(0, c[0] + 1);
        }
        c
    } else if mutation_kind == 7 {
        // nudge first element down (if above min)
        let mut c = candidates;
        if c[0] > 1 {
            c.set(0, c[0] - 1);
        }
        c
    } else if mutation_kind == 8 && candidates.len() >= 2 {
        // swap first and last elements
        let first = candidates[0];
        let last_val = candidates[candidates.len() - 1];
        let mut c = candidates;
        let last_idx = c.len() - 1;
        c.set(0, last_val);
        c.set(last_idx, first);
        c
    } else if mutation_kind == 9 {
        // set first element to a power-of-two-like value: 1
        let mut c = candidates;
        c.set(0, 1);
        c
    } else {
        candidates // fallback
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

fn mutate(candidates: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(candidates, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_candidates(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 10_000_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2275);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |candidates: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", candidates);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::largest_combination(candidates.clone());
        writeln!(out, "{}", json!({"input": {"candidates": candidates}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![16, 17, 71, 62, 12, 24, 14],
        vec![8, 8],
    ];
    for seed_vec in &example_seeds {
        for mk in 0..=10u8 {
            let result = mutate(seed_vec.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Boundary and interesting seeds
    let special_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![10_000_000],
        vec![1, 1],
        vec![10_000_000, 10_000_000],
        vec![1, 2, 4, 8, 16],
        vec![7, 7, 7, 7],
        vec![1048576, 2097152, 4194304],
        vec![5_000_000, 5_000_001],
    ];
    for seed_vec in &special_seeds {
        for mk in 0..=10u8 {
            let result = mutate(seed_vec.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // max-ish
        };
        let seed_vec = random_candidates(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(seed_vec, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
