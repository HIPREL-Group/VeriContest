use vstd::prelude::*;

verus! {

pub fn generate_test_case(dimensions: Vec<Vec<i32>>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= dimensions.len() <= 100,
        forall|i: int| 0 <= i < dimensions.len() ==> dimensions[i].len() == 2,
        forall|i: int| 0 <= i < dimensions.len() ==> 1 <= #[trigger] dimensions[i][0] <= 100,
        forall|i: int| 0 <= i < dimensions.len() ==> 1 <= #[trigger] dimensions[i][1] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i][0] <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i][1] <= 100,
{
    if mutation_kind == 0 {
        // identity
        dimensions
    } else if mutation_kind == 1 {
        // set first element's length to 100 (max boundary)
        let mut d = dimensions;
        let mut row = d[0].clone();
        row.set(0, 100);
        d.set(0, row);
        assert(d[0].len() == 2);
        assert(d[0][0] == 100);
        d
    } else if mutation_kind == 2 {
        // set first element's width to 1 (min boundary)
        let mut d = dimensions;
        let mut row = d[0].clone();
        row.set(1, 1);
        d.set(0, row);
        assert(d[0].len() == 2);
        assert(d[0][1] == 1);
        d
    } else if mutation_kind == 3 {
        // set first element to [1, 1] (min area)
        let mut d = dimensions;
        let mut row = d[0].clone();
        row.set(0, 1);
        row.set(1, 1);
        d.set(0, row);
        assert(d[0].len() == 2);
        d
    } else if mutation_kind == 4 {
        // set first element to [100, 100] (max area and diagonal)
        let mut d = dimensions;
        let mut row = d[0].clone();
        row.set(0, 100);
        row.set(1, 100);
        d.set(0, row);
        assert(d[0].len() == 2);
        d
    } else if mutation_kind == 5 {
        // swap length and width of first element
        let mut d = dimensions;
        let row = d[0].clone();
        let l = row[0];
        let w = row[1];
        let mut new_row = row;
        new_row.set(0, w);
        new_row.set(1, l);
        d.set(0, new_row);
        assert(d[0].len() == 2);
        d
    } else if mutation_kind == 6 && dimensions.len() < 100 {
        // grow: append [1, 1]
        let mut d = dimensions;
        let mut new_row: Vec<i32> = Vec::new();
        new_row.push(1);
        new_row.push(1);
        assert(new_row.len() == 2);
        assert(new_row[0] == 1);
        assert(new_row[1] == 1);
        d.push(new_row);
        assert(d[d.len() - 1].len() == 2);
        d
    } else if mutation_kind == 7 && dimensions.len() > 1 {
        // shrink: remove last element
        let mut d = dimensions;
        d.pop();
        d
    } else if mutation_kind == 8 {
        // set first element to [50, 50] (middle values)
        let mut d = dimensions;
        let mut row = d[0].clone();
        row.set(0, 50);
        row.set(1, 50);
        d.set(0, row);
        assert(d[0].len() == 2);
        d
    } else {
        // fallback: identity
        dimensions
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

fn mutate(dimensions: Vec<Vec<i32>>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(dimensions, mutation_kind)
}

fn random_dimensions(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut dims = Vec::with_capacity(n);
    for _ in 0..n {
        let l = rng.gen_range_i64(1, 100) as i32;
        let w = rng.gen_range_i64(1, 100) as i32;
        dims.push(vec![l, w]);
    }
    dims
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

    let mut emit = |dims: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", dims);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::area_of_max_diagonal(dims.clone());
        writeln!(out, "{}", json!({"input": {"dimensions": dims}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![9, 3], vec![8, 6]],
        vec![vec![3, 4], vec![4, 3]],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Seed inputs for mutation
    let seeds: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1, 1]],
        vec![vec![100, 100]],
        vec![vec![1, 100]],
        vec![vec![100, 1]],
        vec![vec![50, 50]],
        vec![vec![1, 1], vec![100, 100]],
        vec![vec![10, 10], vec![10, 10]],
        vec![vec![1, 1], vec![1, 1], vec![1, 1]],
        vec![vec![99, 99], vec![100, 100]],
        vec![vec![7, 24], vec![24, 7]],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random dimensions with varying sizes and random mutations
    for _ in 0..60 {
        let n = match rng.gen_range_usize(0, 4) {
            0 => 1,                                   // tiny
            1 => rng.gen_range_usize(1, 5),           // small
            2 => rng.gen_range_usize(6, 20),          // medium
            3 => rng.gen_range_usize(21, 50),         // large
            _ => rng.gen_range_usize(51, 100),        // max
        };
        let dims = random_dimensions(&mut rng, n);
        let mk = rng.gen_range_usize(0, 8) as u8;
        emit(mutate(dims, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity inputs
    while count < target_count {
        let n = rng.gen_range_usize(1, 100);
        let dims = random_dimensions(&mut rng, n);
        emit(mutate(dims, 0), &mut seen, &mut out, &mut count);
    }
}
