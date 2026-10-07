use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: i32, seed_b: i32, seed_c: i32, mutation_kind: u8) -> (res: (i32, i32, i32))
    requires
        1 <= seed_a <= 100,
        1 <= seed_b <= 100,
        1 <= seed_c <= 100,
        seed_a != seed_b,
        seed_b != seed_c,
        seed_a != seed_c,
    ensures
        1 <= res.0 <= 100,
        1 <= res.1 <= 100,
        1 <= res.2 <= 100,
        res.0 != res.1,
        res.1 != res.2,
        res.0 != res.2,
{
    if mutation_kind == 0 {
        // identity
        (seed_a, seed_b, seed_c)
    } else if mutation_kind == 1 {
        // swap a and b
        (seed_b, seed_a, seed_c)
    } else if mutation_kind == 2 {
        // swap a and c
        (seed_c, seed_b, seed_a)
    } else if mutation_kind == 3 {
        // swap b and c
        (seed_a, seed_c, seed_b)
    } else if mutation_kind == 4 && 1 != seed_b && 1 != seed_c {
        // set a to min boundary
        (1, seed_b, seed_c)
    } else if mutation_kind == 5 && 100 != seed_b && 100 != seed_c {
        // set a to max boundary
        (100, seed_b, seed_c)
    } else if mutation_kind == 6 && seed_a < 100 && seed_a + 1 != seed_b && seed_a + 1 != seed_c {
        // nudge a up
        (seed_a + 1, seed_b, seed_c)
    } else if mutation_kind == 7 && seed_a > 1 && seed_a - 1 != seed_b && seed_a - 1 != seed_c {
        // nudge a down
        (seed_a - 1, seed_b, seed_c)
    } else if mutation_kind == 8 {
        // fixed consecutive triple (min boundary)
        (1, 2, 3)
    } else if mutation_kind == 9 {
        // fixed consecutive triple (max boundary)
        (98, 99, 100)
    } else if mutation_kind == 10 {
        // fixed wide spread
        (1, 50, 100)
    } else if mutation_kind == 11 {
        // fixed gap-of-2
        (1, 3, 5)
    } else {
        // fallback: identity
        (seed_a, seed_b, seed_c)
    }
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

/// Generate three distinct values in [1, 100].
fn random_triple(rng: &mut Rng) -> (i32, i32, i32) {
    loop {
        let a = rng.gen_range_i64(1, 100) as i32;
        let b = rng.gen_range_i64(1, 100) as i32;
        let c = rng.gen_range_i64(1, 100) as i32;
        if a != b && b != c && a != c {
            return (a, b, c);
        }
    }
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 12;

    let mut emit = |a: i32, b: i32, c: i32, seen: &mut HashSet<(i32,i32,i32)>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target || !seen.insert((a, b, c)) {
            return;
        }
        let result = Solution::num_moves_stones(a, b, c);
        writeln!(out, "{}", json!({"input": {"a": a, "b": b, "c": c}, "output": result})).unwrap();
        *count += 1;
    };

    // Seed pool: example inputs + interesting triples
    let seeds: Vec<(i32, i32, i32)> = vec![
        // Examples from description
        (1, 2, 5),
        (4, 3, 2),
        (3, 5, 1),
        // Consecutive triples
        (1, 2, 3),
        (50, 51, 52),
        (98, 99, 100),
        // Gap of 2 (min_moves = 1)
        (1, 3, 5),
        (10, 12, 14),
        (96, 98, 100),
        // Wide spread (min_moves = 2)
        (1, 50, 100),
        (1, 2, 100),
        (1, 99, 100),
        // Boundary values
        (1, 2, 100),
        (1, 99, 100),
        (1, 50, 99),
        // Various orderings
        (100, 1, 50),
        (50, 100, 1),
        (3, 1, 2),
        // Near-consecutive
        (10, 11, 13),
        (10, 12, 13),
        // Large gaps
        (1, 2, 99),
        (2, 99, 100),
    ];

    // Apply every mutation to every seed
    for &(sa, sb, sc) in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (a, b, c) = generate_test_case(sa, sb, sc, mk);
            emit(a, b, c, &mut seen, &mut out, &mut count);
        }
        if count >= target { break; }
    }

    // Random seeds with random mutations
    while count < target {
        let (sa, sb, sc) = random_triple(&mut rng);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (a, b, c) = generate_test_case(sa, sb, sc, mk);
        emit(a, b, c, &mut seen, &mut out, &mut count);
    }
}
