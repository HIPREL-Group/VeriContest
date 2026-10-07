use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 500,
        1 <= seed_k <= seed_n,
    ensures
        1 <= res.1 <= res.0 <= 500,
{
    let n: i32;
    let k: i32;

    if mutation_kind == 0 {
        // identity
        n = seed_n;
        k = seed_k;
    } else if mutation_kind == 1 && seed_n < 500 {
        // nudge n up
        n = seed_n + 1;
        k = seed_k;
    } else if mutation_kind == 2 && seed_n > 1 && seed_k < seed_n {
        // nudge n down (ensure k <= n still holds)
        n = seed_n - 1;
        k = seed_k;
    } else if mutation_kind == 3 && seed_k < seed_n {
        // nudge k up
        n = seed_n;
        k = seed_k + 1;
    } else if mutation_kind == 4 && seed_k > 1 {
        // nudge k down
        n = seed_n;
        k = seed_k - 1;
    } else if mutation_kind == 5 {
        // k = 1
        n = seed_n;
        k = 1;
    } else if mutation_kind == 6 {
        // k = n
        n = seed_n;
        k = seed_n;
    } else if mutation_kind == 7 {
        // n = 1, k = 1
        n = 1;
        k = 1;
    } else if mutation_kind == 8 {
        // max boundary: n = 500, k clamped
        n = 500;
        k = seed_k;
    } else if mutation_kind == 9 {
        // halve n, clamp k
        let half_n = if seed_n / 2 >= 1 { seed_n / 2 } else { 1i32 };
        n = half_n;
        k = if seed_k <= half_n { seed_k } else { half_n };
    } else if mutation_kind == 10 && seed_n <= 250 {
        // double n
        n = seed_n * 2;
        k = seed_k;
    } else if mutation_kind == 11 {
        // swap: n stays, k = n - k + 1 (mirror k)
        n = seed_n;
        k = seed_n - seed_k + 1;
    } else {
        // fallback: identity
        n = seed_n;
        k = seed_k;
    }

    (n, k)
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
}

struct Solution;
include!("../code.rs");

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
    let mut count = 0;
    let num_mutations: u8 = 12;

    // Example inputs from description + boundary seeds
    let seeds: Vec<(i32, i32)> = vec![
        (5, 2),     // example 1
        (6, 5),     // example 2
        (1, 1),     // minimum
        (500, 500), // max n, k = n
        (500, 1),   // max n, k = 1
        (2, 1),
        (2, 2),
        (3, 1),
        (3, 2),
        (3, 3),
        (10, 3),
        (10, 7),
        (100, 1),
        (100, 50),
        (100, 100),
        (250, 125),
        (499, 499),
        (500, 250),
    ];

    // Seed pool × mutation_kind
    for &(sn, sk) in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (n, k) = generate_test_case(sn, sk, mk);
            if seen.insert((n, k)) {
                let result = Solution::find_the_winner(n, k);
                writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
                count += 1;
            }
        }
        if count >= target { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let sn = rng.gen_range_i64(1, 500) as i32;
        let sk = rng.gen_range_i64(1, sn as i64) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n, k)) {
            let result = Solution::find_the_winner(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }
}
