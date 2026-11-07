use vstd::prelude::*;

verus! {

pub fn generate_test_case(height: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= height.len() <= 100_000,
        forall|i: int| 0 <= i < height.len() ==> 0 <= #[trigger] height[i] <= 10_000,
    ensures
        2 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        height
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut h = height;
        h.set(0, 0);
        h
    } else if mutation_kind == 2 {
        // set first element to 10_000 (max boundary)
        let mut h = height;
        h.set(0, 10_000);
        h
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut h = height;
        let last = h.len() - 1;
        h.set(last, 0);
        h
    } else if mutation_kind == 4 {
        // set last element to 10_000
        let mut h = height;
        let last = h.len() - 1;
        h.set(last, 10_000);
        h
    } else if mutation_kind == 5 {
        // set all elements to 0
        let mut h = height;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == height.len(),
                2 <= h.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> h[j] == 0i32,
                forall|j: int| i <= j < h.len() ==> h[j] == height[j],
            decreases h.len() - i,
        {
            h.set(i, 0);
            i += 1;
        }
        h
    } else if mutation_kind == 6 {
        // set all elements to 10_000
        let mut h = height;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == height.len(),
                2 <= h.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> h[j] == 10_000i32,
                forall|j: int| i <= j < h.len() ==> h[j] == height[j],
            decreases h.len() - i,
        {
            h.set(i, 10_000);
            i += 1;
        }
        h
    } else if mutation_kind == 7 && height.len() < 100_000 {
        // grow by one element (push 0)
        let mut h = height;
        h.push(0);
        h
    } else if mutation_kind == 8 && height.len() > 2 {
        // shrink by one element (pop)
        let mut h = height;
        h.pop();
        h
    } else if mutation_kind == 9 {
        // nudge first element up (if < 10_000)
        let mut h = height;
        if h[0] < 10_000 {
            h.set(0, h[0] + 1);
        }
        h
    } else if mutation_kind == 10 {
        // nudge first element down (if > 0)
        let mut h = height;
        if h[0] > 0 {
            h.set(0, h[0] - 1);
        }
        h
    } else if mutation_kind == 11 && height.len() >= 2 {
        // swap first and last elements
        let mut h = height;
        let last = h.len() - 1;
        let first_val = h[0];
        let last_val = h[last];
        h.set(0, last_val);
        h.set(last, first_val);
        h
    } else {
        // fallback: identity
        height
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

extern crate serde_json;
use serde_json::json;

fn random_height(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut h = Vec::with_capacity(len);
    for _ in 0..len {
        h.push(rng.gen_range_i64(0, 10_000) as i32);
    }
    h
}

fn mutate(height: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(height, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |height: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", height);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_area(height.clone());
        writeln!(out, "{}", json!({"input": {"height": height}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 8, 6, 2, 5, 4, 8, 3, 7],
        vec![1, 1],
    ];

    // Interesting seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![0, 0],
        vec![10_000, 10_000],
        vec![0, 10_000],
        vec![10_000, 0],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![0, 0, 0, 0, 0],
        vec![10_000, 10_000, 10_000],
        vec![1, 10_000, 1],
        vec![10_000, 1, 10_000],
        vec![0, 10_000, 0, 10_000],
        vec![5000, 5000, 5000, 5000],
        vec![1, 2],
        vec![9999, 10_000],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Emit examples with identity mutation
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    for i in 0..80 {
        if count >= target_count { break; }
        let n = match i % 5 {
            0 => rng.gen_range_usize(2, 5),        // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // big
        };
        let h = random_height(&mut rng, n);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = mutate(h, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining
    while count < target_count {
        let n = rng.gen_range_usize(2, 1000);
        let h = random_height(&mut rng, n);
        emit(mutate(h, 0), &mut seen, &mut out, &mut count);
    }
}
