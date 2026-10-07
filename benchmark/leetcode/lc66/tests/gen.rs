use vstd::prelude::*;

verus! {

pub fn generate_test_case(digits: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= digits.len() <= 100,
        forall|i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
        digits.len() == 1 || digits[0] > 0,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 9,
        result.len() == 1 || result[0] > 0,
{
    if mutation_kind == 0 {
        // identity
        digits
    } else if mutation_kind == 1 {
        // set last digit to 9 (carry test)
        let mut d = digits;
        let last = d.len() - 1;
        d.set(last, 9);
        d
    } else if mutation_kind == 2 {
        // set all digits to 9 (full carry propagation)
        let mut d = digits;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == digits.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 9,
                forall|j: int| i <= j < d.len() ==> d[j] == digits[j],
            decreases d.len() - i,
        {
            d.set(i, 9);
            i += 1;
        }
        d
    } else if mutation_kind == 3 && digits.len() < 100 && digits[0] > 0 {
        // append a 0 digit (grow by one); requires digits[0] > 0 for multi-digit invariant
        let mut d = digits;
        d.push(0);
        d
    } else if mutation_kind == 4 && digits.len() > 1 {
        // remove last digit (shrink by one)
        let mut d = digits;
        d.pop();
        d
    } else if mutation_kind == 5 {
        // set last digit to 0 (no carry)
        let mut d = digits;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 6 {
        // nudge last digit up: if < 9, increment by 1
        let mut d = digits;
        let last = d.len() - 1;
        if d[last] < 9 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge last digit down: if > 0, decrement by 1
        let mut d = digits;
        let last = d.len() - 1;
        if d[last] > 0 {
            d.set(last, d[last] - 1);
        }
        d
    } else {
        digits  // fallback
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
    for i in 0..len {
        if i == 0 && len > 1 {
            digits.push(rng.gen_range_i64(1, 9) as i32);
        } else {
            digits.push(rng.gen_range_i64(0, 9) as i32);
        }
    }
    digits
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let mut rng = Rng::new(66);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let target = 100;

    let mut emit = |digits: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}", digits);
        if *count >= target || !seen.insert(key) {
            return;
        }
        let output = Solution::plus_one(digits.clone());
        writeln!(out, "{}", json!({"input": {"digits": digits}, "output": output})).unwrap();
        *count += 1;
    };

    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![9],
        vec![1, 0, 0],
        vec![9, 9, 9],
        vec![1, 2, 3],
        vec![1],
        vec![5, 5, 5, 5, 5],
        vec![1, 0, 0, 0, 0],
        vec![9, 9, 9, 9, 9, 9, 9, 9, 9, 9],
        vec![4, 3, 2, 1],
        vec![1, 9, 9],
        vec![8, 9, 9],
        vec![2, 0],
        vec![9, 0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed
    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations
    for _ in 0..60 {
        let len = rng.gen_range_usize(1, 100);
        let seed = random_digits(&mut rng, len);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = mutate(seed, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let seed = random_digits(&mut rng, len);
        emit(mutate(seed, 0), &mut seen, &mut out, &mut count);
    }
}
