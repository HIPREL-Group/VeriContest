use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_n: i32,
    seed_w: i32,
    seed_max_weight: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32))
    requires
        1 <= seed_n <= 1000,
        1 <= seed_w <= 1000,
        1 <= seed_max_weight <= 1_000_000_000i32,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= 1000,
        1 <= result.2 <= 1_000_000_000i32,
{
    let n: i32;
    let w: i32;
    let max_weight: i32;

    if mutation_kind == 0 {
        // identity
        n = seed_n;
        w = seed_w;
        max_weight = seed_max_weight;
    } else if mutation_kind == 1 {
        // nudge n up
        n = if seed_n < 1000 { (seed_n + 1) as i32 } else { seed_n };
        w = seed_w;
        max_weight = seed_max_weight;
    } else if mutation_kind == 2 {
        // nudge n down
        n = if seed_n > 1 { (seed_n - 1) as i32 } else { seed_n };
        w = seed_w;
        max_weight = seed_max_weight;
    } else if mutation_kind == 3 {
        // nudge w up
        n = seed_n;
        w = if seed_w < 1000 { (seed_w + 1) as i32 } else { seed_w };
        max_weight = seed_max_weight;
    } else if mutation_kind == 4 {
        // nudge w down
        n = seed_n;
        w = if seed_w > 1 { (seed_w - 1) as i32 } else { seed_w };
        max_weight = seed_max_weight;
    } else if mutation_kind == 5 {
        // nudge max_weight up
        n = seed_n;
        w = seed_w;
        max_weight = if seed_max_weight < 1_000_000_000i32 {
            (seed_max_weight + 1) as i32
        } else {
            seed_max_weight
        };
    } else if mutation_kind == 6 {
        // nudge max_weight down
        n = seed_n;
        w = seed_w;
        max_weight = if seed_max_weight > 1 {
            (seed_max_weight - 1) as i32
        } else {
            seed_max_weight
        };
    } else if mutation_kind == 7 {
        // n = 1 (min boundary)
        n = 1;
        w = seed_w;
        max_weight = seed_max_weight;
    } else if mutation_kind == 8 {
        // n = 1000 (max boundary)
        n = 1000;
        w = seed_w;
        max_weight = seed_max_weight;
    } else if mutation_kind == 9 {
        // w = 1 (min boundary)
        n = seed_n;
        w = 1;
        max_weight = seed_max_weight;
    } else if mutation_kind == 10 {
        // w = 1000 (max boundary)
        n = seed_n;
        w = 1000;
        max_weight = seed_max_weight;
    } else if mutation_kind == 11 {
        // max_weight = 1 (min boundary)
        n = seed_n;
        w = seed_w;
        max_weight = 1;
    } else if mutation_kind == 12 {
        // max_weight = 1_000_000_000 (max boundary)
        n = seed_n;
        w = seed_w;
        max_weight = 1_000_000_000i32;
    } else if mutation_kind == 13 {
        // halve n
        n = if seed_n / 2 >= 1 { seed_n / 2 } else { 1i32 };
        w = seed_w;
        max_weight = seed_max_weight;
    } else if mutation_kind == 14 {
        // double n (clamped)
        n = if seed_n <= 500 { (seed_n * 2) as i32 } else { 1000i32 };
        w = seed_w;
        max_weight = seed_max_weight;
    } else if mutation_kind == 15 {
        // halve w
        n = seed_n;
        w = if seed_w / 2 >= 1 { seed_w / 2 } else { 1i32 };
        max_weight = seed_max_weight;
    } else if mutation_kind == 16 {
        // double w (clamped)
        n = seed_n;
        w = if seed_w <= 500 { (seed_w * 2) as i32 } else { 1000i32 };
        max_weight = seed_max_weight;
    } else if mutation_kind == 17 {
        // halve max_weight
        n = seed_n;
        w = seed_w;
        max_weight = if seed_max_weight / 2 >= 1 {
            seed_max_weight / 2
        } else {
            1i32
        };
    } else if mutation_kind == 18 {
        // all min boundaries
        n = 1;
        w = 1;
        max_weight = 1;
    } else if mutation_kind == 19 {
        // all max boundaries
        n = 1000;
        w = 1000;
        max_weight = 1_000_000_000i32;
    } else {
        // fallback: identity
        n = seed_n;
        w = seed_w;
        max_weight = seed_max_weight;
    }

    (n, w, max_weight)
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
}

struct Solution;
include!("../code.rs");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut rng = Rng::new(seed);
    let num_mutations: u8 = 20;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (2, 3, 15),
        (3, 5, 20),
    ];

    for (n, w, mw) in &examples {
        let result = Solution::max_containers(*n, *w, *mw);
        writeln!(out, "{}", json!({
            "input": {"n": n, "w": w, "maxWeight": mw},
            "output": result
        })).unwrap();
    }

    let mut generated = examples.len();

    // Seed pools for diverse coverage
    let n_seeds: Vec<i32> = vec![1, 2, 3, 10, 31, 32, 100, 500, 999, 1000];
    let w_seeds: Vec<i32> = vec![1, 2, 5, 10, 100, 500, 999, 1000];
    let mw_seeds: Vec<i32> = vec![1, 2, 10, 100, 1000, 999_999, 1_000_000, 999_999_999, 1_000_000_000];

    // Structured sweep: seed pools × mutations
    'outer: for &sn in &n_seeds {
        for &sw in &w_seeds {
            for &smw in &mw_seeds {
                let mk = (rng.next_u64() % num_mutations as u64) as u8;
                let (n, w, mw) = generate_test_case(sn, sw, smw, mk);
                let result = Solution::max_containers(n, w, mw);
                writeln!(out, "{}", json!({
                    "input": {"n": n, "w": w, "maxWeight": mw},
                    "output": result
                })).unwrap();
                generated += 1;
                if generated >= count {
                    break 'outer;
                }
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while generated < count {
        let sn = rng.gen_range_i64(1, 1000) as i32;
        let sw = rng.gen_range_i64(1, 1000) as i32;
        let smw = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, w, mw) = generate_test_case(sn, sw, smw, mk);
        let result = Solution::max_containers(n, w, mw);
        writeln!(out, "{}", json!({
            "input": {"n": n, "w": w, "maxWeight": mw},
            "output": result
        })).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
