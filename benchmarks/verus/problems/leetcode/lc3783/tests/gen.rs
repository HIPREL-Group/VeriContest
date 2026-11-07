use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= 1_000_000_000i32,
    ensures
        1i32 <= result <= 1_000_000_000i32,
{
    if mutation_kind == 0 {
        // identity
        seed
    } else if mutation_kind == 1 && seed < 1_000_000_000 {
        // nudge up
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        // nudge down
        seed - 1
    } else if mutation_kind == 3 {
        // double (if in range)
        if seed <= 500_000_000 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        // halve (at least 1)
        let h = seed / 2;
        if h >= 1 {
            h
        } else {
            1
        }
    } else if mutation_kind == 5 {
        // min boundary
        1
    } else if mutation_kind == 6 {
        // max boundary
        1_000_000_000
    } else if mutation_kind == 7 {
        // near middle
        500_000_000
    } else if mutation_kind == 8 {
        // ones: strip to single digit (seed % 9 + 1 gives 1..9)
        let d = seed % 9;
        d + 1
    } else if mutation_kind == 9 {
        // palindrome-ish: clamp to 1..999_999_999 range via modulo
        if seed <= 999_999_999 {
            seed
        } else {
            999_999_999
        }
    } else {
        // fallback: identity
        seed
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
    let mut emitted = 0usize;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![25, 10, 7];

    // Interesting seed pool: palindromes, repdigits, powers of 10, boundaries
    let interesting: Vec<i32> = vec![
        1, 2, 9, 10, 11, 21, 100, 121, 123, 999,
        1000, 1001, 1234, 9999, 10000, 12321, 99999,
        100000, 100001, 999999, 1000000, 1000000000,
        999999999, 123456789, 987654321, 111111111,
        500000000, 100000001,
    ];

    let num_mutations: u8 = 10;

    // Emit examples first
    for &n in &examples {
        if seen.insert(n) {
            let result = Solution::mirror_distance(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            emitted += 1;
        }
    }

    // Emit interesting seeds × all mutations
    for &s in &interesting {
        for m in 0..num_mutations {
            if emitted >= count { break; }
            let n = generate_test_case(s, m);
            if seen.insert(n) {
                let result = Solution::mirror_distance(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
                emitted += 1;
            }
        }
        if emitted >= count { break; }
    }

    // Fill remaining with random seeds × random mutations
    while emitted < count {
        let s = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let m = rng.gen_u8() % num_mutations;
        let n = generate_test_case(s, m);
        if seen.insert(n) {
            let result = Solution::mirror_distance(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            emitted += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", emitted, out_path);
}
