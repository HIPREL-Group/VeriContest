use vstd::prelude::*;

verus! {

pub fn generate_test_case(citations: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= citations.len() <= 5_000,
        forall|i: int| 0 <= i < citations.len() ==> 0 <= #[trigger] citations[i] <= 1_000,
    ensures
        1 <= result.len() <= 5_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1_000,
{
    if mutation_kind == 0 {
        // identity
        citations
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut c = citations;
        let last = c.len() - 1;
        c.set(last, 0);
        c
    } else if mutation_kind == 2 {
        // set last element to 1000 (max boundary)
        let mut c = citations;
        let last = c.len() - 1;
        c.set(last, 1000);
        c
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut c = citations;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == citations.len(),
                1 <= c.len() <= 5_000,
                forall|j: int| 0 <= j < i ==> c[j] == 0,
                forall|j: int| i <= j < c.len() ==> c[j] == citations[j],
            decreases c.len() - i,
        {
            c.set(i, 0);
            i += 1;
        }
        c
    } else if mutation_kind == 4 {
        // set all elements to 1000
        let mut c = citations;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == citations.len(),
                1 <= c.len() <= 5_000,
                forall|j: int| 0 <= j < i ==> c[j] == 1000,
                forall|j: int| i <= j < c.len() ==> c[j] == citations[j],
            decreases c.len() - i,
        {
            c.set(i, 1000);
            i += 1;
        }
        c
    } else if mutation_kind == 5 && citations.len() < 5_000 {
        // grow: push one element (value 0)
        let mut c = citations;
        c.push(0);
        c
    } else if mutation_kind == 6 && citations.len() > 1 {
        // shrink: pop one element
        let mut c = citations;
        c.pop();
        c
    } else if mutation_kind == 7 {
        // nudge last element up (if < 1000)
        let mut c = citations;
        let last = c.len() - 1;
        if c[last] < 1000 {
            c.set(last, c[last] + 1);
        }
        c
    } else if mutation_kind == 8 {
        // nudge last element down (if > 0)
        let mut c = citations;
        let last = c.len() - 1;
        if c[last] > 0 {
            c.set(last, c[last] - 1);
        }
        c
    } else if mutation_kind == 9 {
        // swap first and last elements
        let mut c = citations;
        let last = c.len() - 1;
        let first_val = c[0];
        let last_val = c[last];
        c.set(0, last_val);
        if last > 0 {
            c.set(last, first_val);
        }
        c
    } else {
        // fallback: identity
        citations
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

fn mutate(citations: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(citations, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_citations(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(274);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |citations: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", citations);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::h_index(citations.clone());
        writeln!(out, "{}", json!({"input": {"citations": citations}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![3, 0, 6, 1, 5],
        vec![1, 3, 1],
    ];
    for s in &example_seeds {
        emit(s.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted boundary seeds
    let boundary_seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1000],
        vec![0, 0, 0],
        vec![1, 1, 1, 1, 1],
        vec![100, 100, 100],
        vec![0, 0, 0, 0, 0],
        vec![1],
        vec![0, 1],
        vec![1, 0],
        vec![1000, 1000, 1000],
        vec![5, 5, 5, 5, 5],
        vec![2, 2, 2],
        vec![10, 20, 30, 40, 50],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &boundary_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse size classes and random mutations
    for i in 0..80 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // max
        };
        let seed_vec = random_citations(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_vec, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target_count {
        let len = rng.gen_range_usize(1, 5000);
        let seed_vec = random_citations(&mut rng, len);
        emit(mutate(seed_vec, 0), &mut seen, &mut out, &mut count);
    }
}
