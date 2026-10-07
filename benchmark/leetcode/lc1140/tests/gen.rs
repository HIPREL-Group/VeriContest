use vstd::prelude::*;

verus! {

pub fn generate_test_case(piles: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= piles.len() <= 100,
        forall|i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 10000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10000,
{
    if mutation_kind == 0 {
        // identity
        piles
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut p = piles;
        p.set(0, 1);
        p
    } else if mutation_kind == 2 {
        // set first element to 10000 (max boundary)
        let mut p = piles;
        p.set(0, 10000);
        p
    } else if mutation_kind == 3 {
        // set last element to 1
        let mut p = piles;
        let last = p.len() - 1;
        p.set(last, 1);
        p
    } else if mutation_kind == 4 {
        // set last element to 10000
        let mut p = piles;
        let last = p.len() - 1;
        p.set(last, 10000);
        p
    } else if mutation_kind == 5 && piles.len() < 100 {
        // grow by one element
        let mut p = piles;
        p.push(1);
        p
    } else if mutation_kind == 6 && piles.len() > 1 {
        // shrink by one element
        let mut p = piles;
        p.pop();
        p
    } else if mutation_kind == 7 {
        // set all elements to 1
        let mut p = piles;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == piles.len(),
                1 <= p.len() <= 100,
                forall|j: int| 0 <= j < i ==> p[j] == 1i32,
                forall|j: int| i <= j < p.len() ==> p[j] == piles[j],
            decreases p.len() - i,
        {
            p.set(i, 1);
            i += 1;
        }
        p
    } else if mutation_kind == 8 {
        // set all elements to 10000
        let mut p = piles;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == piles.len(),
                1 <= p.len() <= 100,
                forall|j: int| 0 <= j < i ==> p[j] == 10000i32,
                forall|j: int| i <= j < p.len() ==> p[j] == piles[j],
            decreases p.len() - i,
        {
            p.set(i, 10000);
            i += 1;
        }
        p
    } else if mutation_kind == 9 {
        // nudge first element up if possible
        let mut p = piles;
        if p[0] < 10000 {
            p.set(0, p[0] + 1);
        }
        p
    } else if mutation_kind == 10 {
        // nudge first element down if possible
        let mut p = piles;
        if p[0] > 1 {
            p.set(0, p[0] - 1);
        }
        p
    } else if mutation_kind == 11 && piles.len() >= 2 {
        // swap first and last elements
        let mut p = piles;
        let last = p.len() - 1;
        let first_val = p[0];
        let last_val = p[last];
        p.set(0, last_val);
        p.set(last, first_val);
        p
    } else {
        // fallback: identity
        piles
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

fn mutate(piles: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(piles, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_piles(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut piles = Vec::with_capacity(len);
    for _ in 0..len {
        piles.push(rng.gen_range_i64(1, 10000) as i32);
    }
    piles
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1140);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |piles: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", piles);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::stone_game_ii(piles.clone());
        writeln!(out, "{}", json!({"input": {"piles": piles}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 7, 9, 4, 4],
        vec![1, 2, 3, 4, 5, 100],
    ];

    // Curated seed inputs for diversity
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![10000],
        vec![1, 1],
        vec![10000, 10000],
        vec![1, 2, 3],
        vec![5000, 5000, 5000, 5000],
        vec![1, 10000, 1, 10000, 1],
        vec![100, 200, 300, 400, 500, 600, 700, 800, 900, 1000],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Emit examples with identity mutation first
    for ex in &examples {
        emit(mutate(ex.clone(), 0), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),     // tiny
        (4, 10),    // small
        (11, 30),   // medium
        (31, 60),   // large
        (61, 100),  // max
    ];

    for i in 0..50 {
        let (lo, hi) = size_classes[i % size_classes.len()];
        let len = rng.gen_range_usize(lo, hi);
        let p = random_piles(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        emit(mutate(p, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random piles, identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let p = random_piles(&mut rng, len);
        emit(mutate(p, 0), &mut seen, &mut out, &mut count);
    }
}
