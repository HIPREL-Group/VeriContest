use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u32, mutation_kind: u8) -> (result: u32)
    requires
        0 <= seed <= u32::MAX,
    ensures
        0 <= result <= u32::MAX,
{
    if mutation_kind == 0 {
        seed                                              // identity
    } else if mutation_kind == 1 && seed < u32::MAX {
        seed + 1                                          // nudge up
    } else if mutation_kind == 2 && seed > 0 {
        seed - 1                                          // nudge down
    } else if mutation_kind == 3 {
        if seed <= 2_147_483_647 {
            seed * 2                                      // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2                                          // halve
    } else if mutation_kind == 5 {
        0                                                 // zero
    } else if mutation_kind == 6 {
        u32::MAX                                          // max boundary
    } else if mutation_kind == 7 {
        seed / 10                                         // drop last digit
    } else if mutation_kind == 8 {
        if seed <= 429_496_728 {
            seed * 10                                     // shift left (append 0)
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        seed % 10                                         // keep last digit only
    } else {
        seed                                              // fallback
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

    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        assert!(lo <= hi);
        let range = hi - lo + 1;
        lo + self.next_u64() % range
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
    let examples: Vec<u32> = vec![123, 120];

    // Seed pool: interesting values for digit reversal
    let mut seeds: Vec<u32> = vec![
        0, 1, 10, 100, 1000, 10000, 100000, 1000000,
        9, 99, 999, 9999, 99999, 999999, 9999999,
        12, 21, 1001, 1010, 1234567890,
        u32::MAX, u32::MAX - 1, u32::MAX / 2,
        4294967295, 4294967290, 2147483647, 2147483648,
        1000000000, 1000000001, 123456789, 987654321,
        11, 111, 1111, 11111, 111111, 1111111,
    ];

    // Add example inputs first
    for &x in &examples {
        if generated >= count { break; }
        if seen.insert(x) {
            let output = Solution::reverse(x);
            writeln!(out, "{}", json!({"input": {"x": x}, "output": output})).unwrap();
            generated += 1;
        }
    }

    // Seed pool × mutation kinds
    for &s in &seeds {
        for mk in 0..=10u8 {
            if generated >= count { break; }
            let x = generate_test_case(s, mk);
            if seen.insert(x) {
                let output = Solution::reverse(x);
                writeln!(out, "{}", json!({"input": {"x": x}, "output": output})).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random values
    while generated < count {
        let s = match generated % 5 {
            0 => rng.gen_range_u64(0, 9) as u32,                    // tiny
            1 => rng.gen_range_u64(0, 999) as u32,                  // small
            2 => rng.gen_range_u64(1000, 999_999) as u32,           // medium
            3 => rng.gen_range_u64(1_000_000, 999_999_999) as u32,  // large
            _ => rng.gen_range_u64(1_000_000_000, u32::MAX as u64) as u32, // max range
        };
        let mk = rng.gen_u8() % 11;
        let x = generate_test_case(s, mk);
        if seen.insert(x) {
            let output = Solution::reverse(x);
            writeln!(out, "{}", json!({"input": {"x": x}, "output": output})).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
