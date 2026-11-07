use vstd::prelude::*;

verus! {

pub fn generate_test_case(digits: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= digits.len() <= 10,
        forall|i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
    ensures
        3 <= result.len() <= 10,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 9,
{
    if mutation_kind == 0 {
        // identity
        digits
    } else if mutation_kind == 1 {
        // set last digit to 0
        let mut d = digits;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last digit to 9
        let mut d = digits;
        let last = d.len() - 1;
        d.set(last, 9);
        d
    } else if mutation_kind == 3 {
        // set all digits to the same value (first digit)
        let mut d = digits;
        let val = d[0];
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == digits.len(),
                3 <= d.len() <= 10,
                0 <= val <= 9,
                d[0] == val,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == digits[j],
                forall|j: int| 0 <= j < i ==> 0 <= #[trigger] d[j] <= 9,
                forall|j: int| i <= j < d.len() ==> 0 <= #[trigger] d[j] <= 9,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && digits.len() < 10 {
        // grow by one element (push 0)
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
    } else if mutation_kind == 8 && digits.len() >= 4 {
        // swap first and last elements
        let mut d = digits;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 9 {
        // set all digits to 0
        let mut d = digits;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == digits.len(),
                3 <= d.len() <= 10,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == digits[j],
                forall|j: int| 0 <= j < i ==> 0 <= #[trigger] d[j] <= 9,
                forall|j: int| i <= j < d.len() ==> 0 <= #[trigger] d[j] <= 9,
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else {
        // fallback: identity
        digits
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |digits: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize, target: usize| {
        if *count >= target { return; }
        let key = format!("{:?}", digits);
        if !seen.insert(key) { return; }
        let output = Solution::total_numbers(digits.clone());
        writeln!(out, "{}", json!({"input": {"digits": digits}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 4],
        vec![0, 2, 2],
        vec![6, 6, 6],
        vec![1, 3, 5],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count, count_target);
    }

    // Interesting seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![0, 0, 0],
        vec![9, 9, 9],
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
        vec![2, 4, 6],
        vec![1, 1, 1],
        vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        vec![8, 8, 8, 8],
        vec![1, 2, 3, 4, 5],
        vec![0, 2, 4, 6, 8],
        vec![1, 3, 5, 7, 9],
        vec![5, 5, 5, 5, 5],
        vec![0, 0, 2],
        vec![2, 0, 0],
        vec![9, 8, 7, 6, 5, 4, 3, 2, 1, 0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count, count_target);
        }
    }

    // Random seeds with random mutations across size classes
    while count < count_target {
        let len: usize = match rng.gen_range_usize(0, 4) {
            0 => 3,                                 // minimum
            1 => rng.gen_range_usize(3, 4),         // small
            2 => rng.gen_range_usize(5, 7),         // medium
            3 => rng.gen_range_usize(8, 9),         // large
            _ => 10,                                // maximum
        };
        let s = random_digits(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count, count_target);
    }
}
