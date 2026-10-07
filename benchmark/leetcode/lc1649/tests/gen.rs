use vstd::prelude::*;

verus! {

pub fn generate_test_case(instructions: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= instructions.len() <= 100_000,
        forall|i: int| 0 <= i < instructions.len() ==> 1 <= #[trigger] instructions[i] <= 100_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        instructions
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum boundary)
        let mut h = instructions;
        let last = h.len() - 1;
        h.set(last, 1);
        h
    } else if mutation_kind == 2 {
        // set last element to 100_000 (maximum boundary)
        let mut h = instructions;
        let last = h.len() - 1;
        h.set(last, 100_000);
        h
    } else if mutation_kind == 3 {
        // set all elements to 1 (all same, minimum)
        let mut h = instructions;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == instructions.len(),
                1 <= h.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> h[j] == 1int,
                forall|j: int| i <= j < h.len() ==> h[j] == instructions[j],
            decreases h.len() - i,
        {
            h.set(i, 1);
            i += 1;
        }
        h
    } else if mutation_kind == 4 && instructions.len() < 100_000 {
        // grow by one element (push 50_000)
        let mut h = instructions;
        h.push(50_000);
        h
    } else if mutation_kind == 5 && instructions.len() > 1 {
        // shrink by one element (pop)
        let mut h = instructions;
        h.pop();
        h
    } else if mutation_kind == 6 {
        // nudge last element up: if < 100_000, increment by 1
        let mut h = instructions;
        let last = h.len() - 1;
        if h[last] < 100_000 {
            h.set(last, h[last] + 1);
        }
        h
    } else if mutation_kind == 7 {
        // nudge last element down: if > 1, decrement by 1
        let mut h = instructions;
        let last = h.len() - 1;
        if h[last] > 1 {
            h.set(last, h[last] - 1);
        }
        h
    } else if mutation_kind == 8 && instructions.len() >= 2 {
        // swap first two elements
        let mut h = instructions;
        let tmp = h[0];
        h.set(0, h[1]);
        h.set(1, tmp);
        h
    } else if mutation_kind == 9 {
        // set all elements to 100_000 (all same, maximum)
        let mut h = instructions;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == instructions.len(),
                1 <= h.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> h[j] == 100_000int,
                forall|j: int| i <= j < h.len() ==> h[j] == instructions[j],
            decreases h.len() - i,
        {
            h.set(i, 100_000);
            i += 1;
        }
        h
    } else {
        instructions // fallback
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

fn mutate(instructions: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(instructions, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_instructions(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    v
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

    let mut emit = |instructions: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", instructions);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::create_sorted_array(instructions.clone());
        writeln!(out, "{}", json!({"input": {"instructions": instructions}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 5, 6, 2],                   // example 1 -> 1
        vec![1, 2, 3, 6, 5, 4],             // example 2 -> 3
        vec![1, 3, 3, 3, 2, 4, 2, 1, 2],    // example 3 -> 4
        vec![1],                              // single element
        vec![100_000],                        // single max
        vec![1, 1, 1, 1],                    // all same
        vec![100_000, 100_000, 100_000],     // all same max
        vec![5, 4, 3, 2, 1],                // descending
        vec![1, 2, 3, 4, 5],                // ascending
        vec![1, 100_000],                    // two elements min/max
        vec![100_000, 1],                    // two elements max/min
        vec![50_000, 50_000, 50_000],        // all same middle
        vec![1, 2],                          // sorted pair
        vec![2, 1],                          // reversed pair
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    // Keep sizes small-ish since code.rs is O(n^2)
    for i in 0..60 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 30),       // medium
            3 => rng.gen_range_usize(31, 100),      // large
            _ => rng.gen_range_usize(101, 500),     // bigger
        };
        let s = random_instructions(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 200);
        let s = random_instructions(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
