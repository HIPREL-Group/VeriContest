use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        -2_147_483_648i32 <= seed <= 2_147_483_647i32,
    ensures
        i32::MIN <= result <= i32::MAX,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < i32::MAX {
        seed + 1
    } else if mutation_kind == 2 && seed > i32::MIN {
        seed - 1
    } else if mutation_kind == 3 && seed > i32::MIN {
        -seed
    } else if mutation_kind == 4 {
        if seed >= -1_073_741_824 && seed <= 1_073_741_823 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        seed / 2
    } else if mutation_kind == 6 {
        0
    } else if mutation_kind == 7 {
        i32::MIN
    } else if mutation_kind == 8 {
        i32::MAX
    } else if mutation_kind == 9 {
        if seed > i32::MIN {
            if seed >= 0 { seed } else { -seed }
        } else {
            seed
        }
    } else {
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
    let rng_seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(rng_seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 10;

    // Palindrome-focused seed pool
    let seeds: Vec<i32> = vec![
        // Examples from the problem
        121, -121, 10,
        // Single digits (all palindromes)
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
        // Multi-digit palindromes
        11, 22, 33, 44, 55, 66, 77, 88, 99,
        101, 111, 121, 131, 141, 151, 191, 212, 232, 252,
        1001, 1111, 1221, 1331, 12321, 123321,
        1234321, 12344321,
        // Non-palindromes
        -1, -2, -10, -100, -1000,
        10, 12, 100, 123, 1000, 1234, 10000, 12345,
        // Boundary values
        i32::MAX, i32::MIN, i32::MAX - 1, i32::MIN + 1,
        // Near powers of 10
        999, 1000, 9999, 10000, 99999, 100000, 999999, 1000000,
        // Large palindromes
        1000000001, 1111111111, 1234554321,
    ];

    // Seed pool × mutation_kind
    for &s in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let x = generate_test_case(s, mk);
            if seen.insert(x) {
                let output = Solution::is_palindrome(x);
                writeln!(out, "{}", json!({"input": {"x": x}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let s = rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32;
        let mk = rng.gen_u8() % num_mutations;
        let x = generate_test_case(s, mk);
        if seen.insert(x) {
            let output = Solution::is_palindrome(x);
            writeln!(out, "{}", json!({"input": {"x": x}, "output": output})).unwrap();
            count += 1;
        }
    }
}
