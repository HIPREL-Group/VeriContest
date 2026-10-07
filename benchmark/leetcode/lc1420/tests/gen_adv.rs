use vstd::prelude::*;

verus! {

fn mutate_n(seed_n: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed_n <= 50,
    ensures
        1 <= result <= 50,
{
    if mutation_kind == 1 && seed_n < 50 {
        seed_n + 1
    } else if mutation_kind == 2 && seed_n > 1 {
        seed_n - 1
    } else if mutation_kind == 3 {
        1
    } else if mutation_kind == 4 {
        50
    } else if mutation_kind == 5 && seed_n <= 25 {
        assert(seed_n * 2 <= 50) by(nonlinear_arith)
            requires 1 <= seed_n <= 25,
        {};
        seed_n * 2
    } else if mutation_kind == 6 {
        (seed_n + 1) / 2
    } else {
        seed_n
    }
}

fn mutate_m(seed_m: i32, mutation_kind: u8) -> (result: i32)
    requires
        1 <= seed_m <= 100,
    ensures
        1 <= result <= 100,
{
    if mutation_kind == 7 && seed_m < 100 {
        seed_m + 1
    } else if mutation_kind == 8 && seed_m > 1 {
        seed_m - 1
    } else if mutation_kind == 9 {
        1
    } else if mutation_kind == 10 {
        100
    } else if mutation_kind == 11 && seed_m <= 50 {
        assert(seed_m * 2 <= 100) by(nonlinear_arith)
            requires 1 <= seed_m <= 50,
        {};
        seed_m * 2
    } else if mutation_kind == 12 {
        (seed_m + 1) / 2
    } else {
        seed_m
    }
}

fn mutate_k(seed_k: i32, n: i32, mutation_kind: u8) -> (result: i32)
    requires
        0 <= seed_k <= 50,
        1 <= n <= 50,
    ensures
        0 <= result <= n,
{
    if mutation_kind == 13 && seed_k < n {
        seed_k + 1
    } else if mutation_kind == 14 && seed_k > 0 && seed_k <= n {
        seed_k - 1
    } else if mutation_kind == 15 {
        0
    } else if mutation_kind == 16 {
        n
    } else if mutation_kind == 17 && n >= 1 {
        1
    } else if mutation_kind == 18 {
        assert((n + 1) / 2 <= n) by(nonlinear_arith)
            requires 1 <= n <= 50,
        {};
        (n + 1) / 2
    } else {
        if seed_k <= n { seed_k } else { n }
    }
}

pub fn generate_test_case(seed_n: i32, seed_m: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32, i32))
    requires
        1 <= seed_n <= 50,
        1 <= seed_m <= 100,
        0 <= seed_k <= 50,
    ensures
        1 <= res.0 <= 50,
        1 <= res.1 <= 100,
        0 <= res.2 <= res.0,
{
    let n = mutate_n(seed_n, mutation_kind);
    let m = mutate_m(seed_m, mutation_kind);
    let k = mutate_k(seed_k, n, mutation_kind);
    (n, m, k)
}

} // verus!

use std::collections::HashSet;

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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(200);
    let mut rng = Rng::new(seed);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 19;

    let examples: Vec<(i32, i32, i32)> = vec![
        (2, 3, 1),
        (5, 2, 3),
        (9, 1, 1),
    ];
    for &(n, m, k) in &examples {
        if count >= goal { break; }
        if seen.insert((n, m, k)) {
            println!("{{\"n\":{n},\"m\":{m},\"k\":{k}}}");
            count += 1;
        }
    }

    let seed_pool: Vec<(i32, i32, i32)> = vec![
        (1, 1, 0), (1, 1, 1), (1, 100, 1), (1, 100, 0),
        (50, 1, 1), (50, 1, 0), (50, 100, 0), (50, 100, 50),
        (50, 100, 1), (50, 100, 25), (50, 50, 50),
        (2, 2, 1), (2, 2, 2), (5, 5, 3), (10, 10, 5),
        (10, 100, 10), (20, 50, 10), (30, 30, 15),
        (50, 100, 49), (50, 100, 50), (1, 50, 1),
        (3, 3, 2), (5, 10, 5), (10, 1, 1),
        (25, 50, 12), (40, 80, 20), (50, 2, 1),
        (50, 2, 2), (10, 100, 1), (10, 100, 10),
    ];

    for &(sn, sm, sk) in &seed_pool {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (n, m, k) = generate_test_case(sn, sm, sk, mk);
            if seen.insert((n, m, k)) {
                println!("{{\"n\":{n},\"m\":{m},\"k\":{k}}}");
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        let sn = rng.gen_range_i64(1, 50) as i32;
        let sm = rng.gen_range_i64(1, 100) as i32;
        let sk = rng.gen_range_i64(0, sn as i64) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, m, k) = generate_test_case(sn, sm, sk, mk);
        if seen.insert((n, m, k)) {
            println!("{{\"n\":{n},\"m\":{m},\"k\":{k}}}");
            count += 1;
        }
    }
}
