use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a_seed: i32,
    digits: Vec<i32>,
    mutation_kind: u8,
) -> (result: (i32, Vec<i32>))
    requires
        1 <= a_seed <= i32::MAX,
        1 <= digits.len() <= 2000,
        forall|j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
        digits[0] > 0,
    ensures
        1 <= result.0 <= i32::MAX,
        1 <= result.1.len() <= 2000,
        forall|j: int| 0 <= j < result.1.len() ==> 0 <= #[trigger] result.1[j] <= 9,
        result.1[0] > 0,
{
    if mutation_kind == 0 {
        // identity
        (a_seed, digits)
    } else if mutation_kind == 1 && a_seed < i32::MAX {
        // nudge a up
        (a_seed + 1, digits)
    } else if mutation_kind == 2 && a_seed > 1 {
        // nudge a down
        (a_seed - 1, digits)
    } else if mutation_kind == 3 {
        // a = 1
        (1, digits)
    } else if mutation_kind == 4 {
        // a = i32::MAX
        (i32::MAX, digits)
    } else if mutation_kind == 5 {
        // set last digit to 9
        let mut d = digits;
        let last = d.len() - 1;
        d.set(last, 9);
        (a_seed, d)
    } else if mutation_kind == 6 {
        // set all digits to 9
        let mut d = digits;
        let mut i: usize = 0;
        let first_val: i32 = 9;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == digits.len(),
                1 <= d.len() <= 2000,
                forall|j: int| 0 <= j < i ==> d[j] == 9,
                forall|j: int| #![trigger d[j]] i <= j < d.len() ==> d[j] == digits[j],
            decreases d.len() - i,
        {
            d.set(i, 9);
            i += 1;
        }
        (a_seed, d)
    } else if mutation_kind == 7 {
        // set last digit to 0 (keeping first > 0 since len >= 1 and first untouched)
        let mut d = digits;
        let last = d.len() - 1;
        if last > 0 {
            d.set(last, 0);
        }
        // if len == 1, first digit must stay > 0, so no-op
        (a_seed, d)
    } else if mutation_kind == 8 && digits.len() < 2000 && digits[0] > 0 {
        // grow: append a 0 digit
        let mut d = digits;
        d.push(0);
        (a_seed, d)
    } else if mutation_kind == 9 && digits.len() > 1 {
        // shrink: remove last digit
        let mut d = digits;
        d.pop();
        (a_seed, d)
    } else if mutation_kind == 10 {
        // set first digit to 1 (minimum leading digit)
        let mut d = digits;
        d.set(0, 1);
        (a_seed, d)
    } else if mutation_kind == 11 {
        // a halve
        let new_a = if a_seed / 2 >= 1 { a_seed / 2 } else { 1i32 };
        (new_a, digits)
    } else if mutation_kind == 12 {
        // a double (if fits)
        if a_seed <= 1_073_741_823 {
            (a_seed * 2, digits)
        } else {
            (a_seed, digits)
        }
    } else {
        // fallback: identity
        (a_seed, digits)
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

fn make_digits(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut d = Vec::with_capacity(len);
    // first digit 1..9
    d.push(rng.gen_range_i64(1, 9) as i32);
    for _ in 1..len {
        d.push(rng.gen_range_i64(0, 9) as i32);
    }
    d
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut generated = 0usize;

    // Example test cases from description.md
    let examples: Vec<(i32, Vec<i32>)> = vec![
        (2, vec![3]),
        (2, vec![1, 0]),
        (1, vec![4, 3, 3, 8, 5, 2]),
    ];
    for (a, b) in &examples {
        if generated >= count { break; }
        let output = Solution::super_pow(*a, b.clone());
        writeln!(out, "{}", json!({"input": {"a": a, "b": b}, "output": output})).unwrap();
        generated += 1;
    }

    // Interesting a values
    let a_pool: Vec<i32> = vec![
        1, 2, 3, 5, 7, 10, 100, 1000, 1337, 1338,
        i32::MAX, i32::MAX - 1, 2_147_483_646,
    ];

    // Generate with seed pool × mutations
    for &a_val in &a_pool {
        for mk in 0..=12u8 {
            if generated >= count { break; }
            // size class for digits
            let dlen = match generated % 5 {
                0 => 1,
                1 => rng.gen_range_usize(1, 3),
                2 => rng.gen_range_usize(1, 10),
                3 => rng.gen_range_usize(10, 100),
                _ => rng.gen_range_usize(100, 2000),
            };
            let digits = make_digits(&mut rng, dlen);
            let (a, b) = generate_test_case(a_val, digits, mk);
            let output = Solution::super_pow(a, b.clone());
            writeln!(out, "{}", json!({"input": {"a": a, "b": b}, "output": output})).unwrap();
            generated += 1;
        }
        if generated >= count { break; }
    }

    // Fill remaining with random
    while generated < count {
        let a_val = rng.gen_range_i64(1, i32::MAX as i64) as i32;
        let mk = rng.gen_u8() % 13;
        let dlen = match generated % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(1, 20),
            3 => rng.gen_range_usize(20, 200),
            _ => rng.gen_range_usize(200, 2000),
        };
        let digits = make_digits(&mut rng, dlen);
        let (a, b) = generate_test_case(a_val, digits, mk);
        let output = Solution::super_pow(a, b.clone());
        writeln!(out, "{}", json!({"input": {"a": a, "b": b}, "output": output})).unwrap();
        generated += 1;
    }
}
