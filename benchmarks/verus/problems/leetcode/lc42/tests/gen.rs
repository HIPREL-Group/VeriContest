use vstd::prelude::*;

verus! {

pub fn generate_test_case(height: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= height.len() <= 20_000,
        forall|i: int| 0 <= i < height.len() ==> 0 <= #[trigger] height[i] <= 100_000,
    ensures
        1 <= result.len() <= 20_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100_000,
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
        // set first element to 100_000 (max boundary)
        let mut h = height;
        h.set(0, 100_000);
        h
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut h = height;
        let last = h.len() - 1;
        h.set(last, 0);
        h
    } else if mutation_kind == 4 {
        // set last element to 100_000
        let mut h = height;
        let last = h.len() - 1;
        h.set(last, 100_000);
        h
    } else if mutation_kind == 5 {
        // set all elements to 0 (no water trapped)
        let mut h = height;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == height.len(),
                1 <= h.len() <= 20_000,
                forall|j: int| 0 <= j < i ==> h[j] == 0,
                forall|j: int| i <= j < h.len() ==> h[j] == height[j],
            decreases h.len() - i,
        {
            h.set(i, 0);
            i += 1;
        }
        h
    } else if mutation_kind == 6 {
        // set all elements to 100_000 (no water trapped, flat top)
        let mut h = height;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == height.len(),
                1 <= h.len() <= 20_000,
                forall|j: int| 0 <= j < i ==> h[j] == 100_000,
                forall|j: int| i <= j < h.len() ==> h[j] == height[j],
            decreases h.len() - i,
        {
            h.set(i, 100_000);
            i += 1;
        }
        h
    } else if mutation_kind == 7 && height.len() < 20_000 {
        // grow: push a 0
        let mut h = height;
        h.push(0);
        h
    } else if mutation_kind == 8 && height.len() > 1 {
        // shrink: pop last element
        let mut h = height;
        h.pop();
        h
    } else if mutation_kind == 9 && height.len() >= 2 {
        // swap first two elements
        let mut h = height;
        let a = h[0];
        let b = h[1];
        h.set(0, b);
        h.set(1, a);
        h
    } else if mutation_kind == 10 {
        // nudge first element up (if < 100_000)
        let mut h = height;
        if h[0] < 100_000 {
            h.set(0, h[0] + 1);
        }
        h
    } else if mutation_kind == 11 {
        // nudge first element down (if > 0)
        let mut h = height;
        if h[0] > 0 {
            h.set(0, h[0] - 1);
        }
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

fn mutate(height: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(height, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_height(rng: &mut Rng, len: usize, val_lo: i64, val_hi: i64) -> Vec<i32> {
    let mut h = Vec::with_capacity(len);
    for _ in 0..len {
        h.push(rng.gen_range_i64(val_lo, val_hi) as i32);
    }
    h
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

    let mut emit = |height: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", height);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::trap(height.clone());
        writeln!(out, "{}", json!({"input": {"height": height}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let seeds: Vec<Vec<i32>> = vec![
        vec![0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1],
        vec![4, 2, 0, 3, 2, 5],
        // Edge cases
        vec![0],
        vec![100_000],
        vec![0, 0],
        vec![1, 0, 1],
        vec![3, 0, 3],
        vec![0, 100_000, 0],
        vec![100_000, 0, 100_000],
        vec![1, 2, 3, 4, 5],           // ascending (no water)
        vec![5, 4, 3, 2, 1],           // descending (no water)
        vec![5, 0, 5],                 // simple pool
        vec![3, 0, 0, 0, 3],           // wide pool
        vec![1, 0, 2, 0, 3, 0, 2, 0, 1], // multiple pools
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with varied sizes and mutations
    for i in 0..200 {
        if count >= target {
            break;
        }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),          // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 20_000),  // max
        };

        // Vary value ranges for diversity
        let (val_lo, val_hi): (i64, i64) = match i % 4 {
            0 => (0, 10),         // small values
            1 => (0, 1000),       // medium values
            2 => (0, 100_000),    // full range
            _ => (0, 1),          // binary (0 or 1)
        };

        let h = random_height(&mut rng, n, val_lo, val_hi);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = mutate(h, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target {
        let n = rng.gen_range_usize(1, 20_000);
        let h = random_height(&mut rng, n, 0, 100_000);
        emit(mutate(h, 0), &mut seen, &mut out, &mut count);
    }
}
