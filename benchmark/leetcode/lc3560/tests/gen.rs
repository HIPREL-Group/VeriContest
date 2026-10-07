use vstd::prelude::*;

verus! {

pub fn generate_test_case(k_seed: i32, n_seed: i32, m_seed: i32, mutation_kind: u8) -> (res: (i32, i32, i32))
    requires
        2 <= k_seed <= 100_000,
        1 <= n_seed <= 200_000,
        1 <= m_seed <= 200_000,
    ensures
        2 <= res.2 <= 100_000,
        1 <= res.0 <= 2 * res.2,
        1 <= res.1 <= 2 * res.2,
        res.0 <= res.2 || res.1 <= res.2,
{
    let k = k_seed;

    // Clamp n and m into [1, 2*k]
    let n_clamped: i32 = if n_seed > 2 * k { 2 * k } else { n_seed };
    let m_clamped: i32 = if m_seed > 2 * k { 2 * k } else { m_seed };

    if mutation_kind == 0 {
        // Default: if both > k, clamp m to k
        let n = n_clamped;
        let m = if n > k && m_clamped > k { k } else { m_clamped };
        (n, m, k)
    } else if mutation_kind == 1 {
        // If both > k, clamp n to k instead
        let m = m_clamped;
        let n = if m > k && n_clamped > k { k } else { n_clamped };
        (n, m, k)
    } else if mutation_kind == 2 {
        // n = 1 (minimum n)
        (1i32, m_clamped, k)
    } else if mutation_kind == 3 {
        // m = 1 (minimum m)
        (n_clamped, 1i32, k)
    } else if mutation_kind == 4 {
        // n = k (boundary)
        (k, m_clamped, k)
    } else if mutation_kind == 5 {
        // m = k (boundary)
        (n_clamped, k, k)
    } else if mutation_kind == 6 {
        // n = 2*k (max), forces m <= k
        let m = if m_clamped > k { k } else { m_clamped };
        (2i32 * k, m, k)
    } else if mutation_kind == 7 {
        // m = 2*k (max), forces n <= k
        let n = if n_clamped > k { k } else { n_clamped };
        (n, 2i32 * k, k)
    } else if mutation_kind == 8 {
        // Both at k (equal, on boundary)
        (k, k, k)
    } else if mutation_kind == 9 {
        // Both at 1 (minimum)
        (1i32, 1i32, k)
    } else if mutation_kind == 10 {
        // n = 2*k, m = 1 (extreme split)
        (2i32 * k, 1i32, k)
    } else if mutation_kind == 11 {
        // n = 1, m = 2*k (extreme split reversed)
        (1i32, 2i32 * k, k)
    } else {
        // Fallback: both clamped to <= k
        let n = if n_clamped > k { k } else { n_clamped };
        let m = if m_clamped > k { k } else { m_clamped };
        (n, m, k)
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
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        self.gen_range_i64(lo as i64, hi as i64) as i32
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
    let mut emitted = 0usize;
    let num_mutations: u8 = 13;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (6, 5, 5),
        (4, 4, 6),
    ];
    for &(n, m, k) in &examples {
        if seen.insert((n, m, k)) {
            let result = Solution::min_cutting_cost(n, m, k);
            writeln!(out, "{}", json!({"input": {"n": n, "m": m, "k": k}, "output": result})).unwrap();
            emitted += 1;
        }
    }

    // Seed pool: interesting k values × interesting n/m seeds
    let k_seeds: Vec<i32> = vec![
        2, 3, 5, 10, 50, 100, 1000, 10_000, 50_000, 100_000,
    ];
    let nm_seeds: Vec<i32> = vec![
        1, 2, 3, 5, 10, 50, 100, 1000, 10_000, 50_000, 100_000, 200_000,
    ];

    // Seed pool × mutation_kind
    for &k in &k_seeds {
        for &ns in &nm_seeds {
            for &ms in &nm_seeds {
                for mk in 0..num_mutations {
                    if emitted >= count { break; }
                    let ns_c = ns.min(200_000);
                    let ms_c = ms.min(200_000);
                    let (n, m, k_out) = generate_test_case(k, ns_c, ms_c, mk);
                    if seen.insert((n, m, k_out)) {
                        let result = Solution::min_cutting_cost(n, m, k_out);
                        writeln!(out, "{}", json!({"input": {"n": n, "m": m, "k": k_out}, "output": result})).unwrap();
                        emitted += 1;
                    }
                }
            }
        }
    }

    // Fill remaining with random inputs
    while emitted < count {
        // Vary k across size classes
        let k = match emitted % 5 {
            0 => rng.gen_range_i32(2, 5),
            1 => rng.gen_range_i32(2, 100),
            2 => rng.gen_range_i32(100, 1000),
            3 => rng.gen_range_i32(1000, 10_000),
            _ => rng.gen_range_i32(10_000, 100_000),
        };
        let n_seed = rng.gen_range_i32(1, 2 * k);
        let m_seed = rng.gen_range_i32(1, 2 * k);
        let mk = rng.gen_u8() % num_mutations;
        let (n, m, k_out) = generate_test_case(k, n_seed, m_seed, mk);
        if seen.insert((n, m, k_out)) {
            let result = Solution::min_cutting_cost(n, m, k_out);
            writeln!(out, "{}", json!({"input": {"n": n, "m": m, "k": k_out}, "output": result})).unwrap();
            emitted += 1;
        }
    }
}
