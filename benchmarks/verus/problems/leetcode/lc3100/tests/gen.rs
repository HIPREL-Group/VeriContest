use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_bottles: i32,
    seed_exchange: i32,
    mutation_kind: u8,
) -> (result: (i32, i32))
    requires
        1 <= seed_bottles <= 100,
        1 <= seed_exchange <= 100,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
{
    let num_bottles: i32;
    let num_exchange: i32;

    if mutation_kind == 0 {
        // Identity
        num_bottles = seed_bottles;
        num_exchange = seed_exchange;
    } else if mutation_kind == 1 {
        // Nudge +1 (clamp to 100)
        num_bottles = if seed_bottles < 100 { seed_bottles + 1 } else { seed_bottles };
        num_exchange = seed_exchange;
    } else if mutation_kind == 2 {
        // Nudge -1 (clamp to 1)
        num_bottles = if seed_bottles > 1 { seed_bottles - 1 } else { seed_bottles };
        num_exchange = seed_exchange;
    } else if mutation_kind == 3 {
        // Nudge exchange +1
        num_bottles = seed_bottles;
        num_exchange = if seed_exchange < 100 { seed_exchange + 1 } else { seed_exchange };
    } else if mutation_kind == 4 {
        // Nudge exchange -1
        num_bottles = seed_bottles;
        num_exchange = if seed_exchange > 1 { seed_exchange - 1 } else { seed_exchange };
    } else if mutation_kind == 5 {
        // Both at minimum boundary
        num_bottles = 1;
        num_exchange = 1;
    } else if mutation_kind == 6 {
        // Both at maximum boundary
        num_bottles = 100;
        num_exchange = 100;
    } else if mutation_kind == 7 {
        // Min bottles, seed exchange
        num_bottles = 1;
        num_exchange = seed_exchange;
    } else if mutation_kind == 8 {
        // Max bottles, seed exchange
        num_bottles = 100;
        num_exchange = seed_exchange;
    } else if mutation_kind == 9 {
        // Seed bottles, min exchange
        num_bottles = seed_bottles;
        num_exchange = 1;
    } else if mutation_kind == 10 {
        // Seed bottles, max exchange
        num_bottles = seed_bottles;
        num_exchange = 100;
    } else if mutation_kind == 11 {
        // Halve both
        let half_b = seed_bottles / 2;
        let half_e = seed_exchange / 2;
        num_bottles = if half_b >= 1 { half_b } else { 1 };
        num_exchange = if half_e >= 1 { half_e } else { 1 };
    } else if mutation_kind == 12 {
        // Double (clamped)
        let double_b = if seed_bottles <= 50 { seed_bottles * 2 } else { 100 };
        let double_e = if seed_exchange <= 50 { seed_exchange * 2 } else { 100 };
        num_bottles = double_b;
        num_exchange = double_e;
    } else if mutation_kind == 13 {
        // Swap parameters
        num_bottles = seed_exchange;
        num_exchange = seed_bottles;
    } else {
        // Fallback: identity
        num_bottles = seed_bottles;
        num_exchange = seed_exchange;
    }

    (num_bottles, num_exchange)
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
        (13, 6),
        (10, 3),
    ];

    for &(nb, ne) in &examples {
        if generated >= count { break; }
        if seen.insert((nb, ne)) {
            let output = Solution::max_bottles_drunk(nb, ne);
            writeln!(out, "{}", json!({"input": {"numBottles": nb, "numExchange": ne}, "output": output})).unwrap();
            generated += 1;
        }
    }

    // Interesting seed values covering boundaries
    let interesting: Vec<i32> = vec![1, 2, 3, 5, 10, 25, 50, 75, 99, 100];

    // Generate from interesting seeds with all mutation kinds
    for &sb in &interesting {
        for &se in &interesting {
            for mk in 0..=13u8 {
                if generated >= count { break; }
                let (nb, ne) = generate_test_case(sb, se, mk);
                if seen.insert((nb, ne)) {
                    let output = Solution::max_bottles_drunk(nb, ne);
                    writeln!(out, "{}", json!({"input": {"numBottles": nb, "numExchange": ne}, "output": output})).unwrap();
                    generated += 1;
                }
            }
            if generated >= count { break; }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random sampling
    while generated < count {
        let sb = rng.gen_range_i64(1, 100) as i32;
        let se = rng.gen_range_i64(1, 100) as i32;
        let mk = rng.gen_u8() % 14;
        let (nb, ne) = generate_test_case(sb, se, mk);
        if seen.insert((nb, ne)) {
            let output = Solution::max_bottles_drunk(nb, ne);
            writeln!(out, "{}", json!({"input": {"numBottles": nb, "numExchange": ne}, "output": output})).unwrap();
            generated += 1;
        }
    }
}
