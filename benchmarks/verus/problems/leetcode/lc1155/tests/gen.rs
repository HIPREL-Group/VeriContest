use vstd::prelude::*;

verus! {

fn mutate_n(seed_n: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed_n <= 30,
    ensures
        1 <= result <= 30,
{
    if mutation_kind == 1 && seed_n < 30 {
        seed_n + 1
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1
    } else if mutation_kind == 3 {
        1
    } else if mutation_kind == 4 {
        30
    } else if mutation_kind == 5 && seed_n <= 15 {
        assert(seed_n * 2 <= 30) by(nonlinear_arith)
            requires 1 <= seed_n <= 15,
        {};
        seed_n * 2
    } else if mutation_kind == 6 {
        (seed_n + 1) / 2
    } else {
        seed_n
    }
}

fn mutate_k(seed_k: i32, seed_n: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed_k <= 30,
        1 <= seed_n <= 30,
    ensures
        1 <= result <= 30,
{
    if mutation_kind == 7 && seed_k < 30 {
        seed_k + 1
    } else if mutation_kind == 8 && seed_k > 1 {
        seed_k - 1
    } else if mutation_kind == 9 {
        1
    } else if mutation_kind == 10 {
        30
    } else if mutation_kind == 11 {
        seed_n
    } else {
        seed_k
    }
}

fn mutate_target(seed_target: i32, seed_n: i32, seed_k: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed_target <= 1000,
        1 <= seed_n <= 30,
        1 <= seed_k <= 30,
    ensures
        1 <= result <= 1000,
{
    if mutation_kind == 12 && seed_target < 1000 {
        seed_target + 1
    } else if mutation_kind == 13 && seed_target > 1 {
        seed_target - 1
    } else if mutation_kind == 14 {
        1
    } else if mutation_kind == 15 {
        1000
    } else if mutation_kind == 16 && seed_target <= 500 {
        assert(seed_target * 2 <= 1000) by(nonlinear_arith)
            requires 1 <= seed_target <= 500,
        {};
        seed_target * 2
    } else if mutation_kind == 17 {
        (seed_target + 1) / 2
    } else if mutation_kind == 18 {
        seed_n
    } else if mutation_kind == 19 {
        assert(seed_n * seed_k <= 900) by(nonlinear_arith)
            requires 1 <= seed_n <= 30, 1 <= seed_k <= 30,
        {};
        assert(seed_n * seed_k >= 1) by(nonlinear_arith)
            requires 1 <= seed_n <= 30, 1 <= seed_k <= 30,
        {};
        seed_n * seed_k
    } else {
        seed_target
    }
}

pub fn generate_test_case(seed_n: i32, seed_k: i32, seed_target: i32, mutation_kind: u8) -> (res: (i32, i32, i32))
    ensures
        1 <= res.0 <= 30,
        1 <= res.1 <= 30,
        1 <= res.2 <= 1000,
{
    let seed_n = if seed_n < 1 { 1 } else if seed_n > 30 { 30 } else { seed_n };
    let seed_k = if seed_k < 1 { 1 } else if seed_k > 30 { 30 } else { seed_k };
    let seed_target = if seed_target < 1 { 1 } else if seed_target > 1000 { 1000 } else { seed_target };
    let n = mutate_n(seed_n, mutation_kind);
    let k = mutate_k(seed_k, seed_n, mutation_kind);
    let target = mutate_target(seed_target, seed_n, seed_k, mutation_kind);
    (n, k, target)
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
    let num_mutations: u8 = 20;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (1, 6, 3),
        (2, 6, 7),
        (30, 30, 500),
    ];
    for &(n, k, t) in &examples {
        if count >= goal { break; }
        if seen.insert((n, k, t)) {
            let output = Solution::num_rolls_to_target(n, k, t);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k, "target": t}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: interesting combinations
    let seed_pool: Vec<(i32, i32, i32)> = vec![
        (1, 1, 1), (1, 1, 2), (1, 6, 1), (1, 6, 6), (1, 6, 7),
        (1, 30, 1), (1, 30, 15), (1, 30, 30), (1, 30, 31),
        (2, 6, 2), (2, 6, 12), (2, 6, 13),
        (5, 6, 5), (5, 6, 15), (5, 6, 30),
        (10, 10, 10), (10, 10, 55), (10, 10, 100),
        (30, 1, 30), (30, 1, 1), (30, 30, 30), (30, 30, 900),
        (15, 15, 100), (15, 15, 225), (20, 20, 200),
        (1, 1, 1000), (30, 30, 1000), (30, 30, 1),
    ];

    // Seed pool × mutation_kind
    for &(sn, sk, st) in &seed_pool {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (n, k, t) = generate_test_case(sn, sk, st, mk);
            if seen.insert((n, k, t)) {
                let output = Solution::num_rolls_to_target(n, k, t);
                writeln!(out, "{}", json!({"input": {"n": n, "k": k, "target": t}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let sn = rng.gen_range_i64(1, 30) as i32;
        let sk = rng.gen_range_i64(1, 30) as i32;
        let st = rng.gen_range_i64(1, 1000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k, t) = generate_test_case(sn, sk, st, mk);
        if seen.insert((n, k, t)) {
            let output = Solution::num_rolls_to_target(n, k, t);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k, "target": t}, "output": output})).unwrap();
            count += 1;
        }
    }
}
