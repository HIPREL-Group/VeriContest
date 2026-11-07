use vstd::prelude::*;

verus! {

pub fn generate_test_case(ratings: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= ratings.len() <= 20_000,
        forall|i: int| 0 <= i < ratings.len() ==> 0 <= #[trigger] ratings[i] <= 20_000,
    ensures
        1 <= result.len() <= 20_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 20_000,
{
    if mutation_kind == 0 {
        // identity
        ratings
    } else if mutation_kind == 1 {
        // set first element to 0 (boundary low)
        let mut r = ratings;
        r.set(0, 0);
        r
    } else if mutation_kind == 2 {
        // set first element to 20000 (boundary high)
        let mut r = ratings;
        r.set(0, 20_000);
        r
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut r = ratings;
        let last = r.len() - 1;
        r.set(last, 0);
        r
    } else if mutation_kind == 4 {
        // set last element to 20000
        let mut r = ratings;
        let last = r.len() - 1;
        r.set(last, 20_000);
        r
    } else if mutation_kind == 5 {
        // set all elements equal to first element (flat ratings)
        let mut r = ratings;
        let val = r[0];
        let mut i: usize = 1;
        while i < r.len()
            invariant
                1 <= i <= r.len(),
                r.len() == ratings.len(),
                1 <= r.len() <= 20_000,
                0 <= val <= 20_000,
                forall|j: int| 0 <= j < i ==> r[j] == val,
                forall|j: int| i <= j < r.len() ==> r[j] == ratings[j],
                forall|j: int| i <= j < r.len() ==> 0 <= #[trigger] r[j] <= 20_000,
            decreases r.len() - i,
        {
            r.set(i, val);
            i += 1;
        }
        r
    } else if mutation_kind == 6 && ratings.len() < 20_000 {
        // grow by one element (push 0)
        let mut r = ratings;
        r.push(0);
        r
    } else if mutation_kind == 7 && ratings.len() > 1 {
        // shrink by one element (pop)
        let mut r = ratings;
        r.pop();
        r
    } else if mutation_kind == 8 {
        // nudge first element up: if < 20000, increment
        let mut r = ratings;
        if r[0] < 20_000 {
            r.set(0, r[0] + 1);
        }
        r
    } else if mutation_kind == 9 {
        // nudge first element down: if > 0, decrement
        let mut r = ratings;
        if r[0] > 0 {
            r.set(0, r[0] - 1);
        }
        r
    } else if mutation_kind == 10 && ratings.len() >= 2 {
        // swap first two elements
        let mut r = ratings;
        let a = r[0];
        let b = r[1];
        r.set(0, b);
        r.set(1, a);
        r
    } else {
        // fallback: identity
        ratings
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

fn mutate(ratings: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(ratings, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_ratings(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut ratings = Vec::with_capacity(len);
    for _ in 0..len {
        ratings.push(rng.gen_range_i64(0, 20_000) as i32);
    }
    ratings
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(135);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |ratings: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", ratings);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::candy(ratings.clone());
        writeln!(out, "{}", json!({"input": {"ratings": ratings}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 0, 2],
        vec![1, 2, 2],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds for diversity
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],                            // single element, min value
        vec![20000],                        // single element, max value
        vec![5],                            // single element, mid value
        vec![0, 0],                         // two equal elements
        vec![0, 1],                         // two ascending
        vec![1, 0],                         // two descending
        vec![1, 2, 3, 4, 5],               // strictly ascending
        vec![5, 4, 3, 2, 1],               // strictly descending
        vec![3, 3, 3, 3, 3],               // all equal
        vec![1, 3, 2, 4, 1],               // valley and peak
        vec![1, 2, 1, 2, 1],               // alternating
        vec![0, 0, 0, 0, 0],               // all zeros
        vec![20000, 20000, 20000],          // all max
        vec![0, 20000, 0, 20000],           // alternating boundary
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // very large
        };
        let s = random_ratings(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
