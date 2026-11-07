use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    differences: Vec<i32>,
    lower: i32,
    upper: i32,
    mutation_kind: u8,
) -> (ret: (Vec<i32>, i32, i32))
    requires
        1 <= differences.len() <= 100_000,
        -100_000 <= lower <= upper <= 100_000,
        forall|i: int| 0 <= i < differences.len() ==> -100_000 <= #[trigger] differences[i] <= 100_000,
    ensures
        1 <= ret.0.len() <= 100_000,
        -100_000 <= ret.1 <= ret.2 <= 100_000,
        forall|i: int| 0 <= i < ret.0.len() ==> -100_000 <= #[trigger] ret.0[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (differences, lower, upper)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = differences;
        d.set(0, 0);
        (d, lower, upper)
    } else if mutation_kind == 2 {
        // set first element to max boundary
        let mut d = differences;
        d.set(0, 100_000);
        (d, lower, upper)
    } else if mutation_kind == 3 {
        // set first element to min boundary
        let mut d = differences;
        d.set(0, -100_000);
        (d, lower, upper)
    } else if mutation_kind == 4 && differences.len() < 100_000 {
        // grow by one element (push 0)
        let mut d = differences;
        d.push(0);
        (d, lower, upper)
    } else if mutation_kind == 5 && differences.len() > 1 {
        // shrink by one element
        let mut d = differences;
        d.pop();
        (d, lower, upper)
    } else if mutation_kind == 6 {
        // squeeze range: set lower = upper
        (differences, upper, upper)
    } else if mutation_kind == 7 {
        // widen range: set lower = -100_000, upper = 100_000
        (differences, -100_000i32, 100_000i32)
    } else if mutation_kind == 8 {
        // set all elements to 0 (constant differences)
        let mut d = differences;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == differences.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == differences[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        (d, lower, upper)
    } else if mutation_kind == 9 {
        // negate range bounds
        (differences, -upper, -lower)
    } else if mutation_kind == 10 {
        // nudge last element up (if < 100_000)
        let mut d = differences;
        let last = d.len() - 1;
        if d[last] < 100_000 {
            d.set(last, d[last] + 1);
        }
        (d, lower, upper)
    } else if mutation_kind == 11 {
        // nudge last element down (if > -100_000)
        let mut d = differences;
        let last = d.len() - 1;
        if d[last] > -100_000 {
            d.set(last, d[last] - 1);
        }
        (d, lower, upper)
    } else {
        // fallback identity
        (differences, lower, upper)
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

fn mutate(differences: Vec<i32>, lower: i32, upper: i32, mutation_kind: u8) -> (Vec<i32>, i32, i32) {
    generate_test_case(differences, lower, upper, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_differences(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut diffs = Vec::with_capacity(len);
    for _ in 0..len {
        diffs.push(rng.gen_range_i64(-100_000, 100_000) as i32);
    }
    diffs
}

fn random_bounds(rng: &mut Rng) -> (i32, i32) {
    let a = rng.gen_range_i64(-100_000, 100_000) as i32;
    let b = rng.gen_range_i64(-100_000, 100_000) as i32;
    if a <= b { (a, b) } else { (b, a) }
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let mut rng = Rng::new(2145);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let target = 100;

    let mut emit = |differences: Vec<i32>, lower: i32, upper: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?},{},{}", differences, lower, upper);
        if *count >= target || !seen.insert(key) {
            return;
        }
        let output = Solution::number_of_arrays(differences.clone(), lower, upper);
        writeln!(out, "{}", json!({"input": {"differences": differences, "lower": lower, "upper": upper}, "output": output})).unwrap();
        *count += 1;
    };

    // Handcrafted seeds from problem examples
    let seeds: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![1, -3, 4], 1, 6),
        (vec![3, -4, 5, 1, -2], -4, 5),
        (vec![4, -7, 2], 3, 6),
        (vec![0], 0, 0),
        (vec![0], -100_000, 100_000),
        (vec![1], 0, 1),
        (vec![-1], -1, 0),
        (vec![100_000], -100_000, 100_000),
        (vec![-100_000], -100_000, 100_000),
        (vec![1, 1, 1, 1, 1], 0, 10),
        (vec![-1, -1, -1, -1, -1], -10, 0),
        (vec![0, 0, 0], 5, 5),
        (vec![1, -1, 1, -1], -5, 5),
        (vec![100_000, -100_000], -100_000, 100_000),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every seed
    for (diffs, lo, hi) in &seeds {
        for &mk in &mutation_kinds {
            let (rd, rl, rh) = mutate(diffs.clone(), *lo, *hi, mk);
            emit(rd, rl, rh, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 1),
        (2, 5),
        (6, 20),
        (21, 100),
        (101, 1000),
    ];
    for &(lo_len, hi_len) in &size_classes {
        for _ in 0..10 {
            let len = rng.gen_range_usize(lo_len, hi_len);
            let diffs = random_differences(&mut rng, len);
            let (lo, hi) = random_bounds(&mut rng);
            let mk = rng.gen_range_usize(0, 11) as u8;
            let (rd, rl, rh) = mutate(diffs, lo, hi, mk);
            emit(rd, rl, rh, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 500);
        let diffs = random_differences(&mut rng, len);
        let (lo, hi) = random_bounds(&mut rng);
        let (rd, rl, rh) = mutate(diffs, lo, hi, 0);
        emit(rd, rl, rh, &mut seen, &mut out, &mut count);
    }
}
