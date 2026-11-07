use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_m: i32, seed_n: i32, seed_k_raw: i32, mutation_kind: u8) -> (res: (i32, i32, i32))
    ensures
        1 <= res.0 <= 30000,
        1 <= res.1 <= 30000,
        1 <= res.2,
        res.2 as int <= res.0 as int * res.1 as int,
{
    let seed_m = if seed_m < 1 { 1 } else if seed_m > 30000 { 30000 } else { seed_m };
    let seed_n = if seed_n < 1 { 1 } else if seed_n > 30000 { 30000 } else { seed_n };
    let seed_k_raw = if seed_k_raw < 0 { 0 } else { seed_k_raw };
    let m: i32 = if mutation_kind == 1 && seed_m < 30000 {
        seed_m + 1                            // nudge m up
    } else if mutation_kind == 2 && seed_m > 1 {
        seed_m - 1                            // nudge m down
    } else if mutation_kind == 3 {
        1                                     // m = min boundary
    } else if mutation_kind == 4 {
        30000                                 // m = max boundary
    } else if mutation_kind == 5 {
        seed_n                                // m = n (square table)
    } else {
        seed_m                                // identity
    };

    let n: i32 = if mutation_kind == 6 && seed_n < 30000 {
        seed_n + 1                            // nudge n up
    } else if mutation_kind == 7 && seed_n > 1 {
        seed_n - 1                            // nudge n down
    } else if mutation_kind == 8 {
        1                                     // n = min boundary
    } else if mutation_kind == 9 {
        30000                                 // n = max boundary
    } else if mutation_kind == 10 {
        seed_m                                // n = m (square table)
    } else {
        seed_n                                // identity
    };

    proof {
        assert(1 <= m <= 30000) by {};
        assert(1 <= n <= 30000) by {};
        assert(m as int * n as int <= 30000int * 30000int) by (nonlinear_arith)
            requires 1 <= m <= 30000, 1 <= n <= 30000,
        {};
    }
    let mn: i32 = m * n;

    proof {
        assert(mn >= 1) by (nonlinear_arith)
            requires 1 <= m, 1 <= n, mn == m * n,
        {};
        assert(mn as int <= 900_000_000) by {};
    }

    let k: i32 = if mutation_kind == 11 {
        1                                     // k = 1 (smallest)
    } else if mutation_kind == 12 {
        mn                                    // k = m*n (largest)
    } else if mutation_kind == 13 {
        1 + (mn - 1) / 2                     // k = middle
    } else if mutation_kind == 14 {
        proof {
            assert(m as int <= m as int * n as int) by (nonlinear_arith)
                requires 1 <= m, 1 <= n,
            {};
        }
        m                                     // k = m
    } else if mutation_kind == 15 {
        proof {
            assert(n as int <= m as int * n as int) by (nonlinear_arith)
                requires 1 <= m, 1 <= n,
            {};
        }
        n                                     // k = n
    } else {
        // General: k = 1 + seed_k_raw % mn, giving k in [1, mn]
        let r = seed_k_raw % mn;
        proof {
            assert(0 <= r < mn) by {};
            assert(r as int + 1 <= mn as int) by {};
        }
        1 + r
    };

    proof {
        assert(1 <= k) by {};
        assert(k <= mn) by {};
        assert(k as int <= m as int * n as int) by {};
    }

    (m, n, k)
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
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 16;

    // Example test cases from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (3, 3, 5),
        (2, 3, 6),
    ];
    for (m, n, k) in &examples {
        if seen.insert((*m as i64, *n as i64, *k as i64)) {
            let result = Solution::find_kth_number(*m, *n, *k);
            writeln!(out, "{}", json!({
                "input": {"m": m, "n": n, "k": k},
                "output": result
            })).unwrap();
            count += 1;
        }
    }

    // Seed pool for (m, n) with diverse sizes
    let mn_seeds: Vec<(i32, i32)> = vec![
        (1, 1),
        (1, 30000),
        (30000, 1),
        (30000, 30000),
        (2, 3),
        (3, 3),
        (10, 10),
        (100, 100),
        (1000, 1000),
        (5, 7),
        (7, 5),
        (1, 2),
        (2, 1),
        (100, 1),
        (1, 100),
        (500, 600),
        (10000, 3),
        (3, 10000),
        (29999, 30000),
        (15000, 15000),
    ];

    // Seed pool × mutation_kind
    for &(sm, sn) in &mn_seeds {
        for mk in 0..num_mutations {
            if count >= count_target { break; }
            let sk = rng.gen_range_i64(0, i32::MAX as i64) as i32;
            let (m, n, k) = generate_test_case(sm, sn, sk, mk);
            if seen.insert((m as i64, n as i64, k as i64)) {
                let result = Solution::find_kth_number(m, n, k);
                writeln!(out, "{}", json!({
                    "input": {"m": m, "n": n, "k": k},
                    "output": result
                })).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_target {
        let sm = match count % 5 {
            0 => rng.gen_range_i64(1, 5) as i32,        // tiny
            1 => rng.gen_range_i64(1, 50) as i32,       // small
            2 => rng.gen_range_i64(50, 500) as i32,     // medium
            3 => rng.gen_range_i64(500, 5000) as i32,   // large
            _ => rng.gen_range_i64(5000, 30000) as i32, // max
        };
        let sn = match count % 7 {
            0 => rng.gen_range_i64(1, 5) as i32,
            1 => rng.gen_range_i64(1, 50) as i32,
            2 => rng.gen_range_i64(50, 500) as i32,
            3 => rng.gen_range_i64(500, 5000) as i32,
            4 => rng.gen_range_i64(5000, 30000) as i32,
            5 => 1,
            _ => 30000,
        };
        let sk = rng.gen_range_i64(0, i32::MAX as i64) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (m, n, k) = generate_test_case(sm, sn, sk, mk);
        if seen.insert((m as i64, n as i64, k as i64)) {
            let result = Solution::find_kth_number(m, n, k);
            writeln!(out, "{}", json!({
                "input": {"m": m, "n": n, "k": k},
                "output": result
            })).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases", count);
}
