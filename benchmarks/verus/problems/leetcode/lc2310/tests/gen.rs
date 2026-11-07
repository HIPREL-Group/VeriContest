use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_num: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        0 <= seed_num <= 3000,
        0 <= seed_k <= 9,
    ensures
        0 <= res.0 <= 3000,
        0 <= res.1 <= 9,
{
    let num = if mutation_kind == 0 {
        seed_num                                          // identity
    } else if mutation_kind == 1 && seed_num < 3000 {
        seed_num + 1                                      // nudge up
    } else if mutation_kind == 2 && seed_num > 0 {
        seed_num - 1                                      // nudge down
    } else if mutation_kind == 3 && seed_num <= 1500 {
        seed_num * 2                                      // double
    } else if mutation_kind == 4 {
        seed_num / 2                                      // halve
    } else if mutation_kind == 5 {
        0                                                 // zero
    } else if mutation_kind == 6 {
        3000                                              // max boundary
    } else if mutation_kind == 7 {
        if seed_num <= 2990 {
            seed_num + 10                                 // nudge up by 10
        } else {
            seed_num
        }
    } else {
        seed_num                                          // fallback
    };

    let k = if mutation_kind == 8 && seed_k < 9 {
        seed_k + 1                                        // nudge k up
    } else if mutation_kind == 9 && seed_k > 0 {
        seed_k - 1                                        // nudge k down
    } else if mutation_kind == 10 {
        0                                                 // k = 0
    } else if mutation_kind == 11 {
        9                                                 // k = max
    } else {
        seed_k
    };

    (num, k)
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
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 12;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (58, 9),   // output: 2
        (37, 2),   // output: -1
        (0, 7),    // output: 0
    ];

    for &(num, k) in &examples {
        if count >= target_count { break; }
        if seen.insert((num, k)) {
            let result = Solution::minimum_numbers(num, k);
            writeln!(out, "{}", json!({"input": {"num": num, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary values, interesting cases
    let seed_nums: Vec<i32> = vec![
        0, 1, 2, 3, 5, 9, 10, 11, 19, 20, 50, 58, 99, 100,
        500, 999, 1000, 1500, 2000, 2500, 2999, 3000,
    ];
    let seed_ks: Vec<i32> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Seed pool × mutation_kind
    for &sn in &seed_nums {
        for &sk in &seed_ks {
            for mk in 0..num_mutations {
                if count >= target_count { break; }
                let (num, k) = generate_test_case(sn, sk, mk);
                if seen.insert((num, k)) {
                    let result = Solution::minimum_numbers(num, k);
                    writeln!(out, "{}", json!({"input": {"num": num, "k": k}, "output": result})).unwrap();
                    count += 1;
                }
            }
        }
        if count >= target_count { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let sn = rng.gen_range_i64(0, 3000) as i32;
        let sk = rng.gen_range_i64(0, 9) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (num, k) = generate_test_case(sn, sk, mk);
        if seen.insert((num, k)) {
            let result = Solution::minimum_numbers(num, k);
            writeln!(out, "{}", json!({"input": {"num": num, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }
}
