use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: i128, seed_b: i128, mutation_kind: u8) -> (result: (i128, i128))
    requires
        seed_a >= 1,
        seed_b >= 1,
        seed_a <= 1000000000000000000,
        seed_b <= 1000000000000000000,
        (seed_a as int) * (seed_b as int) <= 1000000000000000000,
    ensures
        result.0 >= 1,
        result.1 >= 1,
        result.0 <= 1000000000000000000,
        result.1 <= 1000000000000000000,
        (result.0 as int) * (result.1 as int) <= 1000000000000000000,
{
    if mutation_kind == 0 {
        // identity
        (seed_a, seed_b)
    } else if mutation_kind == 1 {
        // set a = 1, keep b
        (1i128, seed_b)
    } else if mutation_kind == 2 {
        // keep a, set b = 1
        (seed_a, 1i128)
    } else if mutation_kind == 3 {
        // both 1
        (1i128, 1i128)
    } else if mutation_kind == 4 {
        // max a, b = 1
        (1000000000000000000i128, 1i128)
    } else if mutation_kind == 5 {
        // a = 1, max b
        (1i128, 1000000000000000000i128)
    } else if mutation_kind == 6 && seed_a < 1000000000000000000 {
        // nudge a up, set b = 1
        (seed_a + 1, 1i128)
    } else if mutation_kind == 7 && seed_b < 1000000000000000000 {
        // nudge b up, set a = 1
        (1i128, seed_b + 1)
    } else if mutation_kind == 8 && seed_a > 1 {
        // nudge a down, set b = 1
        (seed_a - 1, 1i128)
    } else if mutation_kind == 9 && seed_b > 1 {
        // nudge b down, set a = 1
        (1i128, seed_b - 1)
    } else if mutation_kind == 10 {
        // a = 2, b = 1
        (2i128, 1i128)
    } else {
        // fallback: identity
        (seed_a, seed_b)
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
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

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);
    let mut generated = 0usize;

    // code.rs loops k from 1 to b, so cap b to keep runtime fast
    let max_b: i128 = 500_000;
    let max_val: i128 = 1_000_000_000_000_000_000;
    let num_mutations: u8 = 11;

    // Example test cases from description.md
    let examples: Vec<(i128, i128)> = vec![
        (1, 1),
        (1, 4),
        (2, 4),
    ];

    for (ea, eb) in &examples {
        if generated >= count { break; }
        let (a, b) = generate_test_case(*ea, *eb, 0);
        let result = Solution::maximum_even_sum(a, b);
        let inp_str = format!("1\n{} {}\n", a, b);
        let out_str = format!("{}\n", result);
        writeln!(out, "{}", json!({"input": inp_str, "output": out_str})).unwrap();
        generated += 1;
    }

    // Interesting fixed seed pairs (b kept small for code.rs feasibility)
    let fixed_pairs: Vec<(i128, i128)> = vec![
        (1, 1),
        (1, 2),
        (2, 1),
        (1, 100000),
        (max_val, 1),
        (1000000000, 1),
        (1, 3),
        (3, 1),
        (2, 2),
        (2, 3),
        (3, 3),
        (6, 6),
        (100, 100),
        (12, 12),
        (7, 7),
        (1, 12),
        (12, 1),
        (999999999999999999, 1),
        (1, 999999),
        (500000000000000000, 2),
        (2, 500000),
    ];

    // Generate from fixed pairs × mutations
    for (sa, sb) in &fixed_pairs {
        for mk in 0..num_mutations {
            if generated >= count { break; }
            let (a, b) = generate_test_case(*sa, *sb, mk);
            // Skip if b is too large for code.rs brute-force
            if b > max_b { continue; }
            let result = Solution::maximum_even_sum(a, b);
            let inp_str = format!("1\n{} {}\n", a, b);
            let out_str = format!("{}\n", result);
            writeln!(out, "{}", json!({"input": inp_str, "output": out_str})).unwrap();
            generated += 1;
        }
        if generated >= count { break; }
    }

    // Fill remaining with random seeds + random mutations
    let mut _attempts = 0usize;
    while generated < count {
        _attempts += 1; if _attempts > 10000 { break; }

        // Generate seed_a in various ranges
        let seed_a = match rng.next_u64() % 5 {
            0 => rng.gen_range_i64(1, 10) as i128,
            1 => rng.gen_range_i64(1, 1000) as i128,
            2 => rng.gen_range_i64(1, 1_000_000) as i128,
            3 => rng.gen_range_i64(1, 1_000_000_000) as i128,
            _ => rng.gen_range_i64(1, max_val as i64) as i128,
        };

        // seed_b capped for runtime, and seed_a * seed_b <= 10^18
        let b_limit = (max_val / seed_a).min(max_b);
        if b_limit < 1 { continue; }
        let seed_b = rng.gen_range_i64(1, b_limit as i64) as i128;

        let mk = rng.gen_u8() % num_mutations;
        let (a, b) = generate_test_case(seed_a, seed_b, mk);

        // Skip if b is too large for code.rs brute-force
        if b > max_b { continue; }

        let result = Solution::maximum_even_sum(a, b);
        let inp_str = format!("1\n{} {}\n", a, b);
        let out_str = format!("{}\n", result);
        writeln!(out, "{}", json!({"input": inp_str, "output": out_str})).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
