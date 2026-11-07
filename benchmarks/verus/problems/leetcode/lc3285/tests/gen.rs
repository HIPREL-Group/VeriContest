use vstd::prelude::*;

verus! {

pub fn generate_test_case(height: Vec<i32>, threshold: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        2 <= height.len() <= 100,
        forall|j: int| 0 <= j < height.len() ==> #[trigger] height[j] >= 1,
        forall|j: int| 0 <= j < height.len() ==> #[trigger] height[j] <= 100,
        1 <= threshold <= 100,
    ensures
        2 <= result.0.len() <= 100,
        forall|j: int| 0 <= j < result.0.len() ==> #[trigger] result.0[j] >= 1,
        forall|j: int| 0 <= j < result.0.len() ==> #[trigger] result.0[j] <= 100,
        1 <= result.1 <= 100,
{
    if mutation_kind == 0 {
        // identity
        (height, threshold)
    } else if mutation_kind == 1 {
        // set first element to 1 (boundary low)
        let mut h = height;
        h.set(0, 1);
        (h, threshold)
    } else if mutation_kind == 2 {
        // set first element to 100 (boundary high)
        let mut h = height;
        h.set(0, 100);
        (h, threshold)
    } else if mutation_kind == 3 {
        // set last element to 1
        let mut h = height;
        let last = h.len() - 1;
        h.set(last, 1);
        (h, threshold)
    } else if mutation_kind == 4 {
        // set last element to 100
        let mut h = height;
        let last = h.len() - 1;
        h.set(last, 100);
        (h, threshold)
    } else if mutation_kind == 5 && height.len() < 100 {
        // grow by one element (push 50)
        let mut h = height;
        h.push(50);
        (h, threshold)
    } else if mutation_kind == 6 && height.len() > 2 {
        // shrink by one element (pop)
        let mut h = height;
        h.pop();
        (h, threshold)
    } else if mutation_kind == 7 {
        // set all elements to threshold + 1 (all stable except index 0)
        let th_plus = if threshold < 100 { (threshold + 1) as i32 } else { 100i32 };
        let mut h = height;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == height.len(),
                2 <= h.len() <= 100,
                1 <= th_plus <= 100,
                forall|j: int| 0 <= j < i ==> h[j] == th_plus,
                forall|j: int| i <= j < h.len() ==> h[j] == height[j],
                forall|j: int| 0 <= j < i ==> #[trigger] h[j] >= 1,
                forall|j: int| 0 <= j < i ==> #[trigger] h[j] <= 100,
                forall|j: int| i <= j < h.len() ==> #[trigger] h[j] >= 1,
                forall|j: int| i <= j < h.len() ==> #[trigger] h[j] <= 100,
            decreases h.len() - i,
        {
            h.set(i, th_plus);
            i += 1;
        }
        (h, threshold)
    } else if mutation_kind == 8 {
        // set all elements to threshold (none stable)
        let mut h = height;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == height.len(),
                2 <= h.len() <= 100,
                1 <= threshold <= 100,
                forall|j: int| 0 <= j < i ==> h[j] == threshold,
                forall|j: int| i <= j < h.len() ==> h[j] == height[j],
                forall|j: int| 0 <= j < i ==> #[trigger] h[j] >= 1,
                forall|j: int| 0 <= j < i ==> #[trigger] h[j] <= 100,
                forall|j: int| i <= j < h.len() ==> #[trigger] h[j] >= 1,
                forall|j: int| i <= j < h.len() ==> #[trigger] h[j] <= 100,
            decreases h.len() - i,
        {
            h.set(i, threshold);
            i += 1;
        }
        (h, threshold)
    } else if mutation_kind == 9 {
        // set threshold to 1 (min boundary)
        (height, 1)
    } else if mutation_kind == 10 {
        // set threshold to 100 (max boundary)
        (height, 100)
    } else if mutation_kind == 11 && height.len() >= 3 {
        // swap first two elements
        let mut h = height;
        let a = h[0];
        let b = h[1];
        h.set(0, b);
        h.set(1, a);
        (h, threshold)
    } else if mutation_kind == 12 {
        // nudge first element up (if < 100)
        let mut h = height;
        if h[0] < 100 {
            h.set(0, h[0] + 1);
        }
        (h, threshold)
    } else if mutation_kind == 13 {
        // nudge first element down (if > 1)
        let mut h = height;
        if h[0] > 1 {
            h.set(0, h[0] - 1);
        }
        (h, threshold)
    } else {
        // fallback: identity
        (height, threshold)
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

fn mutate(height: Vec<i32>, threshold: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(height, threshold, mutation_kind)
}

fn random_height(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut h = Vec::with_capacity(len);
    for _ in 0..len {
        h.push(rng.gen_range_i64(1, 100) as i32);
    }
    h
}

extern crate serde_json;
use serde_json::json;

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

    let mut emit = |height: Vec<i32>, threshold: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", height, threshold);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::stable_mountains(height.clone(), threshold);
        writeln!(out, "{}", json!({"input": {"height": height, "threshold": threshold}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 2, 3, 4, 5], 2),
        (vec![10, 1, 10, 1, 10], 3),
        (vec![10, 1, 10, 1, 10], 10),
    ];

    for (h, t) in &examples {
        emit(h.clone(), *t, &mut seen, &mut out, &mut count);
    }

    // Seed arrays for systematic mutation coverage
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1, 1],
        vec![100, 100],
        vec![1, 100],
        vec![100, 1],
        vec![50, 50, 50],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![100, 1, 100, 1, 100],
        vec![50, 50],
        vec![1, 1, 1, 1, 1],
        vec![99, 100, 1, 2, 50],
    ];

    let thresholds: Vec<i32> = vec![1, 50, 99, 100, 25, 75];
    let mutation_kinds: Vec<u8> = (0..=13).collect();

    // Apply mutations to seeds × thresholds
    for seed_arr in &seed_arrays {
        for &th in &thresholds {
            for &mk in &mutation_kinds {
                let (h, t) = mutate(seed_arr.clone(), th, mk);
                emit(h, t, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random inputs with random mutations across size classes
    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(2, 3),     // tiny
            1 => rng.gen_range_usize(2, 10),    // small
            2 => rng.gen_range_usize(11, 30),   // medium
            3 => rng.gen_range_usize(31, 70),   // large
            _ => rng.gen_range_usize(71, 100),  // max
        };
        let h = random_height(&mut rng, len);
        let th = rng.gen_range_i64(1, 100) as i32;
        let mk = rng.gen_range_usize(0, 13) as u8;
        let (rh, rt) = mutate(h, th, mk);
        emit(rh, rt, &mut seen, &mut out, &mut count);
    }
}
