use vstd::prelude::*;

verus! {

pub fn generate_test_case(left_seed: i32, span_seed: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= left_seed <= 1_000_000,
        0 <= span_seed <= 10_000,
    ensures
        1 <= res.0 <= res.1 <= 1_000_000,
        0 <= res.1 - res.0 <= 10_000,
{
    let bl = left_seed;
    let span = if bl + span_seed > 1_000_000 {
        1_000_000 - bl
    } else {
        span_seed
    };
    let br = bl + span;

    if mutation_kind == 0 {
        (bl, br)
    } else if mutation_kind == 1 {
        // zero span
        (bl, bl)
    } else if mutation_kind == 2 && bl < 1_000_000 {
        // span of 1
        (bl, bl + 1)
    } else if mutation_kind == 3 {
        // push to right boundary
        let nl = if bl < 990_000 { 990_000i32 } else { bl };
        (nl, 1_000_000i32)
    } else if mutation_kind == 4 {
        // push to left boundary
        let nr = if 1 + span_seed <= 1_000_000 {
            1 + span_seed
        } else {
            1_000_000i32
        };
        (1i32, nr)
    } else if mutation_kind == 5 && bl > 1 {
        // nudge left down
        let nl = bl - 1;
        let ns = if nl + span_seed > 1_000_000 {
            1_000_000 - nl
        } else {
            span_seed
        };
        (nl, nl + ns)
    } else if mutation_kind == 6 && bl < 1_000_000 {
        // nudge left up
        let nl = bl + 1;
        let ns = if nl + span_seed > 1_000_000 {
            1_000_000 - nl
        } else {
            span_seed
        };
        (nl, nl + ns)
    } else if mutation_kind == 7 {
        // halve the span
        let hs = span / 2;
        (bl, bl + hs)
    } else if mutation_kind == 8 {
        // max span from bl
        let ms = if 1_000_000 - bl < 10_000 {
            1_000_000 - bl
        } else {
            10_000i32
        };
        (bl, bl + ms)
    } else {
        (bl, br)
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
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (6, 10),
        (10, 15),
    ];
    for (l, r) in &examples {
        if generated >= count { break; }
        let output = Solution::count_prime_set_bits(*l, *r);
        writeln!(out, "{}", json!({"input": {"left": l, "right": r}, "output": output})).unwrap();
        seen.insert((*l, *r));
        generated += 1;
    }

    // Structured seed pool with diverse ranges
    let left_seeds: Vec<i32> = vec![
        1, 2, 3, 10, 100, 1000, 10_000, 100_000, 500_000,
        990_000, 999_990, 1_000_000,
    ];
    let span_seeds: Vec<i32> = vec![
        0, 1, 2, 5, 10, 100, 1000, 5000, 10_000,
    ];

    for &ls in &left_seeds {
        for &ss in &span_seeds {
            if generated >= count { break; }
            for mk in 0..=9u8 {
                if generated >= count { break; }
                let (l, r) = generate_test_case(ls, ss, mk);
                if seen.insert((l, r)) {
                    let output = Solution::count_prime_set_bits(l, r);
                    writeln!(out, "{}", json!({"input": {"left": l, "right": r}, "output": output})).unwrap();
                    generated += 1;
                }
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random
    while generated < count {
        let ls = rng.gen_range_i64(1, 1_000_000) as i32;
        let ss = rng.gen_range_i64(0, 10_000) as i32;
        let mk = rng.gen_u8() % 10;
        let (l, r) = generate_test_case(ls, ss, mk);
        if seen.insert((l, r)) {
            let output = Solution::count_prime_set_bits(l, r);
            writeln!(out, "{}", json!({"input": {"left": l, "right": r}, "output": output})).unwrap();
            generated += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
