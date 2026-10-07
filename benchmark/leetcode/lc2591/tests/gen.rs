use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_money: i32, seed_children: i32, mutation_kind: u8) -> (res: (i32, i32))
    ensures
        1 <= res.0 <= 200,
        2 <= res.1 <= 30,
{
    let seed_money = if seed_money < 1 { 1 } else if seed_money > 200 { 200 } else { seed_money };
    let seed_children = if seed_children < 2 { 2 } else if seed_children > 30 { 30 } else { seed_children };
    let money = if mutation_kind == 0 {
        // Identity
        seed_money
    } else if mutation_kind == 1 && seed_money < 200 {
        // Nudge +1
        seed_money + 1
    } else if mutation_kind == 2 && seed_money > 1 {
        // Nudge -1
        seed_money - 1
    } else if mutation_kind == 3 {
        // Min boundary
        1
    } else if mutation_kind == 4 {
        // Max boundary
        200
    } else if mutation_kind == 5 && seed_money >= 2 && seed_money <= 200 {
        // Halve (clamped to min 1)
        let h = seed_money / 2;
        if h < 1 { 1 } else { h }
    } else if mutation_kind == 6 && seed_money <= 100 {
        // Double (clamped to max 200)
        seed_money * 2
    } else {
        seed_money
    };

    let children = if mutation_kind == 7 && seed_children < 30 {
        // Nudge +1
        seed_children + 1
    } else if mutation_kind == 8 && seed_children > 2 {
        // Nudge -1
        seed_children - 1
    } else if mutation_kind == 9 {
        // Min boundary
        2
    } else if mutation_kind == 10 {
        // Max boundary
        30
    } else if mutation_kind == 11 && seed_children >= 4 {
        // Halve (clamped to min 2)
        let h = seed_children / 2;
        if h < 2 { 2 } else { h }
    } else if mutation_kind == 12 && seed_children <= 15 {
        // Double (clamped to max 30)
        seed_children * 2
    } else {
        seed_children
    };

    (money, children)
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
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let target = 100;
    let num_mutations: u8 = 13;

    let seeds: Vec<(i32, i32)> = vec![
        // Boundary combinations
        (1, 2), (1, 30), (200, 2), (200, 30),
        // money < children (returns -1)
        (2, 3), (3, 5), (5, 10), (1, 10),
        // money == children (everyone gets 1, result 0)
        (2, 2), (10, 10), (30, 30),
        // Exact 8-dollar distributions
        (16, 2), (24, 3), (8, 1),
        // Near-boundary for 4-dollar avoidance rule
        (12, 2), (11, 2), (10, 2),
        // Various mid-range values
        (20, 3), (50, 5), (100, 10), (150, 20),
        // Large money small children
        (200, 2), (200, 3), (200, 5),
        // Small money large children
        (30, 30), (31, 30), (40, 30),
    ];

    // Seed pool × mutation_kind
    for &(sm, sc) in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (money, children) = generate_test_case(sm, sc, mk);
            if seen.insert((money, children)) {
                let result = Solution::dist_money(money, children);
                writeln!(out, "{}", json!({"input": {"money": money, "children": children}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let sm = rng.gen_range_i64(1, 200) as i32;
        let sc = rng.gen_range_i64(2, 30) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (money, children) = generate_test_case(sm, sc, mk);
        if seen.insert((money, children)) {
            let result = Solution::dist_money(money, children);
            writeln!(out, "{}", json!({"input": {"money": money, "children": children}, "output": result})).unwrap();
            count += 1;
        }
    }
}
