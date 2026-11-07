use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_tomato: i32, seed_cheese: i32, mutation_kind: u8) -> (res: (i32, i32))
    ensures
        0 <= res.0 <= 10_000_000,
        0 <= res.1 <= 10_000_000,
{
    let seed_tomato = if seed_tomato < 0 { 0 } else if seed_tomato > 10000000 { 10000000 } else { seed_tomato };
    let seed_cheese = if seed_cheese < 0 { 0 } else if seed_cheese > 10000000 { 10000000 } else { seed_cheese };
    let tomato = if mutation_kind == 0 {
        seed_tomato
    } else if mutation_kind == 1 && seed_tomato < 10_000_000 {
        seed_tomato + 1
    } else if mutation_kind == 2 && seed_tomato > 0 {
        seed_tomato - 1
    } else if mutation_kind == 3 && seed_tomato <= 5_000_000 {
        seed_tomato * 2
    } else if mutation_kind == 4 {
        seed_tomato / 2
    } else if mutation_kind == 5 {
        0
    } else if mutation_kind == 6 {
        10_000_000
    } else {
        seed_tomato
    };

    let cheese = if mutation_kind == 7 && seed_cheese < 10_000_000 {
        seed_cheese + 1
    } else if mutation_kind == 8 && seed_cheese > 0 {
        seed_cheese - 1
    } else if mutation_kind == 9 {
        seed_tomato
    } else if mutation_kind == 10 && seed_cheese <= 5_000_000 {
        seed_cheese * 2
    } else if mutation_kind == 11 {
        seed_cheese / 2
    } else if mutation_kind == 12 {
        0
    } else if mutation_kind == 13 {
        10_000_000
    } else {
        seed_cheese
    };

    (tomato, cheese)
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
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 14;

    let seeds: Vec<(i32, i32)> = vec![
        (16, 7), (17, 4), (4, 17),
        (0, 0), (0, 10_000_000), (10_000_000, 0),
        (10_000_000, 10_000_000), (10_000_000, 5_000_000),
        (40, 10), (4_000_000, 1_000_000),
        (20, 10), (2_000_000, 1_000_000),
        (100, 40), (1000, 300),
        (1, 0), (3, 1), (7, 3), (9_999_999, 5_000_000),
        (2, 0), (0, 1), (2, 1), (4, 1), (0, 5), (10, 5),
    ];

    for &(st, sc) in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (tomato, cheese) = generate_test_case(st, sc, mk);
            if seen.insert((tomato, cheese)) {
                let result = Solution::num_of_burgers(tomato, cheese);
                writeln!(out, "{}", json!({"input": {"tomato_slices": tomato, "cheese_slices": cheese}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        let st = rng.gen_range_i64(0, 10_000_000) as i32;
        let sc = rng.gen_range_i64(0, 10_000_000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (tomato, cheese) = generate_test_case(st, sc, mk);
        if seen.insert((tomato, cheese)) {
            let result = Solution::num_of_burgers(tomato, cheese);
            writeln!(out, "{}", json!({"input": {"tomato_slices": tomato, "cheese_slices": cheese}, "output": result})).unwrap();
            count += 1;
        }
    }
}
