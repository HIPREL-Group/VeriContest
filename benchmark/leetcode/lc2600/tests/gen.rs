use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_ones: i32,
    seed_zeros: i32,
    seed_neg_ones: i32,
    seed_k: i32,
    mutation_kind: u8,
) -> (res: (i32, i32, i32, i32))
    requires
        0 <= seed_ones <= 50,
        0 <= seed_zeros <= 50,
        0 <= seed_neg_ones <= 50,
        0 <= seed_k <= 150,
    ensures
        0 <= res.0 <= 50,
        0 <= res.1 <= 50,
        0 <= res.2 <= 50,
        0 <= res.3 <= res.0 + res.1 + res.2,
{
    let total = seed_ones + seed_zeros + seed_neg_ones;
    let k = if seed_k <= total { seed_k } else { total };

    if mutation_kind == 0 {
        // identity
        (seed_ones, seed_zeros, seed_neg_ones, k)
    } else if mutation_kind == 1 {
        // k = 0
        (seed_ones, seed_zeros, seed_neg_ones, 0)
    } else if mutation_kind == 2 {
        // k = total (pick all items)
        (seed_ones, seed_zeros, seed_neg_ones, total)
    } else if mutation_kind == 3 && seed_ones < 50 {
        // nudge ones up
        let new_ones = seed_ones + 1;
        let new_total = new_ones + seed_zeros + seed_neg_ones;
        let new_k = if seed_k <= new_total { seed_k } else { new_total };
        (new_ones, seed_zeros, seed_neg_ones, new_k)
    } else if mutation_kind == 4 && seed_ones > 0 {
        // nudge ones down
        let new_ones = seed_ones - 1;
        let new_total = new_ones + seed_zeros + seed_neg_ones;
        let new_k = if seed_k <= new_total { seed_k } else { new_total };
        (new_ones, seed_zeros, seed_neg_ones, new_k)
    } else if mutation_kind == 5 && seed_zeros < 50 {
        // nudge zeros up
        let new_zeros = seed_zeros + 1;
        let new_total = seed_ones + new_zeros + seed_neg_ones;
        let new_k = if seed_k <= new_total { seed_k } else { new_total };
        (seed_ones, new_zeros, seed_neg_ones, new_k)
    } else if mutation_kind == 6 && seed_zeros > 0 {
        // nudge zeros down
        let new_zeros = seed_zeros - 1;
        let new_total = seed_ones + new_zeros + seed_neg_ones;
        let new_k = if seed_k <= new_total { seed_k } else { new_total };
        (seed_ones, new_zeros, seed_neg_ones, new_k)
    } else if mutation_kind == 7 && seed_neg_ones < 50 {
        // nudge neg_ones up
        let new_neg = seed_neg_ones + 1;
        let new_total = seed_ones + seed_zeros + new_neg;
        let new_k = if seed_k <= new_total { seed_k } else { new_total };
        (seed_ones, seed_zeros, new_neg, new_k)
    } else if mutation_kind == 8 && seed_neg_ones > 0 {
        // nudge neg_ones down
        let new_neg = seed_neg_ones - 1;
        let new_total = seed_ones + seed_zeros + new_neg;
        let new_k = if seed_k <= new_total { seed_k } else { new_total };
        (seed_ones, seed_zeros, new_neg, new_k)
    } else if mutation_kind == 9 {
        // all zeros
        (0, 0, 0, 0)
    } else if mutation_kind == 10 {
        // all max
        let new_k = if seed_k <= 150 { seed_k } else { 150i32 };
        (50, 50, 50, new_k)
    } else if mutation_kind == 11 {
        // k = num_ones only (best case: all ones picked)
        let k_val = if seed_k <= seed_ones { seed_k } else { seed_ones };
        (seed_ones, seed_zeros, seed_neg_ones, k_val)
    } else if mutation_kind == 12 {
        // k = num_ones + num_zeros (no negatives picked)
        let ones_zeros = seed_ones + seed_zeros;
        let k_val = if seed_k <= ones_zeros { seed_k } else { ones_zeros };
        (seed_ones, seed_zeros, seed_neg_ones, k_val)
    } else if mutation_kind == 13 {
        // halve all seeds
        let h_ones = seed_ones / 2;
        let h_zeros = seed_zeros / 2;
        let h_neg = seed_neg_ones / 2;
        let h_total = h_ones + h_zeros + h_neg;
        let h_k = if seed_k <= h_total { seed_k } else { h_total };
        (h_ones, h_zeros, h_neg, h_k)
    } else if mutation_kind == 14 {
        // no ones, only zeros and neg_ones
        let new_total = seed_zeros + seed_neg_ones;
        let new_k = if seed_k <= new_total { seed_k } else { new_total };
        (0, seed_zeros, seed_neg_ones, new_k)
    } else if mutation_kind == 15 {
        // no zeros
        let new_total = seed_ones + seed_neg_ones;
        let new_k = if seed_k <= new_total { seed_k } else { new_total };
        (seed_ones, 0, seed_neg_ones, new_k)
    } else if mutation_kind == 16 {
        // no neg_ones
        let new_total = seed_ones + seed_zeros;
        let new_k = if seed_k <= new_total { seed_k } else { new_total };
        (seed_ones, seed_zeros, 0, new_k)
    } else {
        // fallback: identity
        (seed_ones, seed_zeros, seed_neg_ones, k)
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
    let mut count = 0;
    let num_mutations: u8 = 17;

    // Example inputs from description.md
    let examples: Vec<(i32, i32, i32, i32)> = vec![
        (3, 2, 0, 2),   // Example 1: output 2
        (3, 2, 0, 4),   // Example 2: output 3
    ];
    for (no, nz, nn, k) in &examples {
        if count >= count_target { break; }
        if seen.insert((*no, *nz, *nn, *k)) {
            let result = Solution::k_items_with_maximum_sum(*no, *nz, *nn, *k);
            writeln!(out, "{}", json!({
                "input": {"numOnes": no, "numZeros": nz, "numNegOnes": nn, "k": k},
                "output": result
            })).unwrap();
            count += 1;
        }
    }

    // Seed pool: representative (ones, zeros, neg_ones, k_seed) tuples
    let seed_pool: Vec<(i32, i32, i32, i32)> = vec![
        (0, 0, 0, 0),
        (50, 50, 50, 150),
        (50, 0, 0, 50),
        (0, 50, 0, 50),
        (0, 0, 50, 50),
        (1, 0, 0, 1),
        (0, 1, 0, 1),
        (0, 0, 1, 1),
        (10, 10, 10, 15),
        (25, 25, 0, 50),
        (50, 50, 50, 0),
        (50, 50, 50, 50),
        (50, 50, 50, 100),
        (1, 1, 1, 3),
        (10, 0, 10, 10),
        (0, 10, 10, 20),
    ];

    // Seed pool × mutation_kind
    for &(so, sz, sn, sk) in &seed_pool {
        for mk in 0..num_mutations {
            if count >= count_target { break; }
            let (no, nz, nn, k) = generate_test_case(so, sz, sn, sk, mk);
            if seen.insert((no, nz, nn, k)) {
                let result = Solution::k_items_with_maximum_sum(no, nz, nn, k);
                writeln!(out, "{}", json!({
                    "input": {"numOnes": no, "numZeros": nz, "numNegOnes": nn, "k": k},
                    "output": result
                })).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < count_target {
        let so = rng.gen_range_i64(0, 50) as i32;
        let sz = rng.gen_range_i64(0, 50) as i32;
        let sn = rng.gen_range_i64(0, 50) as i32;
        let sk = rng.gen_range_i64(0, 150) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (no, nz, nn, k) = generate_test_case(so, sz, sn, sk, mk);
        if seen.insert((no, nz, nn, k)) {
            let result = Solution::k_items_with_maximum_sum(no, nz, nn, k);
            writeln!(out, "{}", json!({
                "input": {"numOnes": no, "numZeros": nz, "numNegOnes": nn, "k": k},
                "output": result
            })).unwrap();
            count += 1;
        }
    }
}
