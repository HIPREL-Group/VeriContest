use vstd::prelude::*;

verus! {

pub fn generate_test_case(digits: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= digits.len() <= 200_000,
        forall|i: int|
            #![trigger digits[i]]
            0 <= i < digits.len() as int ==> 0 <= #[trigger] digits[i] <= 9,
    ensures
        1 <= result.len() <= 200_000,
        forall|i: int|
            #![trigger result[i]]
            0 <= i < result.len() as int ==> 0 <= #[trigger] result[i] <= 9,
{
    if mutation_kind == 0 {
        // identity
        digits
    } else if mutation_kind == 1 {
        // set last digit to 9
        let mut d = digits;
        let last = d.len() - 1;
        d.set(last, 9);
        d
    } else if mutation_kind == 2 {
        // set last digit to 0
        let mut d = digits;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 3 {
        // set all digits to same value (first digit)
        let mut d = digits;
        let val = d[0];
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == digits.len(),
                1 <= d.len() <= 200_000,
                0 <= val <= 9,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| #![trigger d[j]] i <= j < d.len() as int ==> 0 <= d[j] <= 9,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && digits.len() < 200_000 {
        // grow by one element (push a valid digit)
        let mut d = digits;
        let val = d[0]; // reuse first digit (known 0..=9)
        d.push(val);
        d
    } else if mutation_kind == 5 && digits.len() > 1 {
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
        // reverse: swap first and last
        let mut d = digits;
        if d.len() > 1 {
            let first = d[0];
            let last_idx = d.len() - 1;
            let last = d[last_idx];
            d.set(0, last);
            d.set(last_idx, first);
        }
        d
    } else {
        // fallback: identity
        digits
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |digits: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}", digits);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::paint_digits(digits.clone());
        writeln!(out, "{}", json!({
            "input": {"digits": digits},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![0, 4, 0, 4, 2, 5, 5, 2, 4, 6, 4, 4],
        vec![0],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9],
        vec![9, 8],
        vec![9, 8, 7],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Apply every mutation to every example
    for seed_digits in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(seed_digits.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Hand-crafted seeds for edge cases
    let special_seeds: Vec<Vec<i32>> = vec![
        vec![0, 0, 0, 0, 0],           // all zeros
        vec![9, 9, 9, 9, 9],           // all nines
        vec![1],                        // single digit
        vec![5, 5, 5, 5],              // all same
        vec![9, 0, 9, 0],              // alternating extremes
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], // ascending
        vec![9, 8, 7, 6, 5, 4, 3, 2, 1, 0], // descending
    ];

    for seed_digits in &special_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_digits.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Random inputs with diverse sizes and mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),        // tiny
        (4, 10),       // small
        (11, 50),      // medium
        (51, 200),     // large
        (201, 1000),   // very large
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            let len = rng.gen_range_usize(*lo, *hi);
            let seed_digits = random_digits(&mut rng, len);
            let mk = rng.gen_range_usize(0, 8) as u8;
            let result = mutate(seed_digits, mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Fill remaining with random seeds, identity mutation
    while total < count {
        let len = match total % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let seed_digits = random_digits(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        emit(mutate(seed_digits, mk), &mut seen, &mut out, &mut total);
    }
}
