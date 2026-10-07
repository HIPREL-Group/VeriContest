use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_n: i32,
    seed_fp: i32,
    seed_gap: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32))
    requires
        2 <= seed_n <= 28,
        1 <= seed_fp <= 27,
        1 <= seed_gap <= 27,
    ensures
        2 <= result.0 <= 28,
        1 <= result.1 < result.2 <= result.0,
{
    let n = seed_n;
    // Clamp fp to [1, n-1]
    let fp = if seed_fp <= n - 1 { seed_fp } else { n - 1 };
    // Clamp gap to [1, n - fp]
    let max_gap = n - fp;
    let gap = if seed_gap <= max_gap { seed_gap } else { max_gap };
    let sp = fp + gap;

    if mutation_kind == 0 {
        // identity
        (n, fp, sp)
    } else if mutation_kind == 1 {
        // first_player = 1
        let sp2 = if sp >= 2 { sp } else { 2 };
        let sp3 = if sp2 <= n { sp2 } else { n };
        (n, 1, sp3)
    } else if mutation_kind == 2 {
        // second_player = n
        (n, fp, n)
    } else if mutation_kind == 3 {
        // adjacent players
        (n, fp, fp + 1)
    } else if mutation_kind == 4 {
        // extremes: 1 and n
        (n, 1, n)
    } else if mutation_kind == 5 {
        // minimum n = 2
        (2, 1, 2)
    } else if mutation_kind == 6 {
        // maximum n = 28
        let fp2 = if fp <= 27 { fp } else { 27 };
        let sp2 = fp2 + gap;
        let sp3 = if sp2 <= 28 { sp2 } else { 28 };
        (28, fp2, sp3)
    } else if mutation_kind == 7 {
        // swap: fp near end
        let new_fp = n - 1;
        (n, new_fp, n)
    } else if mutation_kind == 8 {
        // middle players
        let mid = n / 2;
        let mid_fp = if mid >= 1 { mid } else { 1 };
        let mid_sp = mid_fp + 1;
        let mid_sp2 = if mid_sp <= n { mid_sp } else { n };
        // ensure fp < sp
        if mid_fp < mid_sp2 {
            (n, mid_fp, mid_sp2)
        } else {
            (n, fp, sp)
        }
    } else {
        // fallback
        (n, fp, sp)
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0;
    let num_mutations: u8 = 10;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32)> = vec![
        (11, 2, 4),
        (5, 1, 5),
    ];
    for (n, fp, sp) in &examples {
        if total >= count { break; }
        if seen.insert((*n, *fp, *sp)) {
            let result = Solution::earliest_and_latest(*n, *fp, *sp);
            writeln!(out, "{}", json!({
                "input": {"n": n, "firstPlayer": fp, "secondPlayer": sp},
                "output": result
            })).unwrap();
            total += 1;
        }
    }

    // Seed pool: cover boundary and interesting cases
    let seed_triples: Vec<(i32, i32, i32)> = vec![
        // (seed_n, seed_fp, seed_gap)
        (2, 1, 1),    // minimal
        (28, 1, 27),  // max n, extremes
        (28, 1, 1),   // max n, adjacent at start
        (28, 27, 1),  // max n, adjacent at end
        (28, 14, 1),  // max n, middle
        (28, 14, 14), // max n, middle to end
        (3, 1, 1),    // small n
        (3, 1, 2),
        (4, 1, 3),
        (4, 2, 1),
        (10, 3, 5),
        (15, 5, 5),
        (20, 1, 19),
        (20, 10, 5),
    ];

    for &(sn, sfp, sg) in &seed_triples {
        for mk in 0..num_mutations {
            if total >= count { break; }
            let (n, fp, sp) = generate_test_case(sn, sfp, sg, mk);
            if seen.insert((n, fp, sp)) {
                let result = Solution::earliest_and_latest(n, fp, sp);
                writeln!(out, "{}", json!({
                    "input": {"n": n, "firstPlayer": fp, "secondPlayer": sp},
                    "output": result
                })).unwrap();
                total += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while total < count {
        let sn = rng.gen_range_i64(2, 28) as i32;
        let sfp = rng.gen_range_i64(1, 27) as i32;
        let sg = rng.gen_range_i64(1, 27) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, fp, sp) = generate_test_case(sn, sfp, sg, mk);
        if seen.insert((n, fp, sp)) {
            let result = Solution::earliest_and_latest(n, fp, sp);
            writeln!(out, "{}", json!({
                "input": {"n": n, "firstPlayer": fp, "secondPlayer": sp},
                "output": result
            })).unwrap();
            total += 1;
        }
    }
}
