use vstd::prelude::*;

verus! {

pub fn generate_test_case(digits: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= digits.len() <= 100,
        forall|i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
    ensures
        3 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 9,
{
    if mutation_kind == 0 {
        // identity
        digits
    } else if mutation_kind == 1 {
        // set last digit to 0 (even-friendly)
        let mut d = digits;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last digit to 9 (odd digit)
        let mut d = digits;
        let last = d.len() - 1;
        d.set(last, 9);
        d
    } else if mutation_kind == 3 {
        // set all digits to the same value (first digit)
        let val = digits[0];
        let mut d = digits;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == digits.len(),
                3 <= d.len() <= 100,
                0 <= val <= 9,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == digits[j],
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && digits.len() < 100 {
        // grow by one element (push a 0)
        let mut d = digits;
        d.push(0);
        d
    } else if mutation_kind == 5 && digits.len() > 3 {
        // shrink by one element (pop)
        let mut d = digits;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge first digit up (if < 9)
        let mut d = digits;
        if d[0] < 9 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge first digit down (if > 0)
        let mut d = digits;
        if d[0] > 0 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 8 {
        // set all digits to 0
        let mut d = digits;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == digits.len(),
                3 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == digits[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 9 {
        // swap first and last elements
        let mut d = digits;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else {
        digits // fallback
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

fn mutate(digits: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(digits, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_digits(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut digits = Vec::with_capacity(len);
    for _ in 0..len {
        digits.push(rng.gen_range_i64(0, 9) as i32);
    }
    digits
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2094);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |digits: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", digits);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::find_even_numbers(digits.clone());
        writeln!(out, "{}", json!({"input": {"digits": digits}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![2, 1, 3, 0],
        vec![2, 2, 8, 8, 2],
        vec![3, 7, 5],
    ];

    // Curated seeds for diversity
    let curated_seeds: Vec<Vec<i32>> = vec![
        vec![0, 0, 0],
        vec![9, 9, 9],
        vec![0, 2, 4],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 0],
        vec![0, 0, 2],
        vec![1, 0, 0],
        vec![2, 4, 6],
        vec![1, 3, 5],
        vec![0, 0, 0, 0, 0],
        vec![5, 5, 5, 5],
        vec![8, 6, 4, 2, 0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Emit example inputs first (identity mutation)
    for seed_digits in &example_seeds {
        emit(seed_digits.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every curated seed
    for seed_digits in &curated_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_digits.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    for i in 0..60 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(3, 5),    // tiny
            1 => rng.gen_range_usize(3, 10),   // small
            2 => rng.gen_range_usize(11, 30),  // medium
            3 => rng.gen_range_usize(31, 70),  // large
            _ => rng.gen_range_usize(71, 100), // max
        };
        let seed_digits = random_digits(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_digits, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = rng.gen_range_usize(3, 100);
        let seed_digits = random_digits(&mut rng, len);
        emit(mutate(seed_digits, 0), &mut seen, &mut out, &mut count);
    }
}
