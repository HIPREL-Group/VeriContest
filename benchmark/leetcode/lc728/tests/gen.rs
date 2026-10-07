use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_left: i32, seed_right: i32, mutation_kind: u8) -> (result: (i32, i32))
    requires
        1 <= seed_left <= 10_000i32,
        1 <= seed_right <= 10_000i32,
    ensures
        1 <= result.0 <= result.1 <= 10_000,
{
    let lo = if seed_left <= seed_right { seed_left } else { seed_right };
    let hi = if seed_left <= seed_right { seed_right } else { seed_left };

    if mutation_kind == 0 {
        // identity
        (lo, hi)
    } else if mutation_kind == 1 {
        // single element range
        (lo, lo)
    } else if mutation_kind == 2 {
        // full range
        (1, 10_000)
    } else if mutation_kind == 3 {
        // left boundary
        (1, hi)
    } else if mutation_kind == 4 {
        // right boundary
        (lo, 10_000)
    } else if mutation_kind == 5 && lo < 10_000 {
        // nudge left up
        (lo + 1, if lo + 1 > hi { lo + 1 } else { hi })
    } else if mutation_kind == 6 && hi > 1 {
        // nudge right down
        (if lo < hi { lo } else { hi - 1 }, hi - 1)
    } else if mutation_kind == 7 {
        // single element at right
        (hi, hi)
    } else if mutation_kind == 8 {
        // min range
        (1, 1)
    } else if mutation_kind == 9 {
        // max range
        (10_000, 10_000)
    } else if mutation_kind == 10 {
        // midpoint single
        let mid = lo + (hi - lo) / 2;
        (mid, mid)
    } else {
        (lo, hi)
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

struct Solution;
include!("../code.rs");

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
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (1, 22),
        (47, 85),
    ];

    for (left, right) in &examples {
        if generated >= count { break; }
        if seen.insert((*left, *right)) {
            let output = Solution::self_dividing_numbers(*left, *right);
            writeln!(out, "{}", json!({"input": {"left": left, "right": right}, "output": output})).unwrap();
            generated += 1;
        }
    }

    // Seed pool: interesting boundary values and ranges
    let seed_values: Vec<i32> = vec![
        1, 2, 9, 10, 11, 22, 48, 55, 66, 77, 100, 128,
        999, 1000, 1111, 5000, 9999, 10_000,
    ];

    for &sl in &seed_values {
        for &sr in &seed_values {
            if generated >= count { break; }
            if sl < 1 || sl > 10_000 || sr < 1 || sr > 10_000 { continue; }
            for mk in 0..=10u8 {
                if generated >= count { break; }
                let (left, right) = generate_test_case(sl, sr, mk);
                if seen.insert((left, right)) {
                    let output = Solution::self_dividing_numbers(left, right);
                    writeln!(out, "{}", json!({"input": {"left": left, "right": right}, "output": output})).unwrap();
                    generated += 1;
                }
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random inputs
    while generated < count {
        let sl = rng.gen_range_i64(1, 10_000) as i32;
        let sr = rng.gen_range_i64(1, 10_000) as i32;
        let mk = rng.gen_u8() % 12;
        let (left, right) = generate_test_case(sl, sr, mk);
        if seen.insert((left, right)) {
            let output = Solution::self_dividing_numbers(left, right);
            writeln!(out, "{}", json!({"input": {"left": left, "right": right}, "output": output})).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases", generated);
}
