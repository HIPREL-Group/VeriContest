use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_n <= 1000000000i32,
        1 <= seed_k <= 1000000000i32,
    ensures
        1 <= res.0 <= 1000000000,
        1 <= res.1 <= res.0,
{
    // Compute n via mutation
    let n: i32 = if mutation_kind == 0 {
        seed_n                                              // identity
    } else if mutation_kind == 1 {
        1i32                                                // minimum n
    } else if mutation_kind == 2 {
        1000000000i32                                       // maximum n
    } else if mutation_kind == 3 && seed_n < 1000000000i32 {
        seed_n + 1                                          // nudge n up
    } else if mutation_kind == 4 && seed_n > 1 {
        seed_n - 1                                          // nudge n down
    } else if mutation_kind == 5 {
        seed_n / 2 + 1                                      // halve n (>= 1)
    } else if mutation_kind == 6 && seed_n <= 500_000_000i32 {
        seed_n * 2                                          // double n
    } else {
        seed_n                                              // fallback
    };

    // Compute k, ensuring 1 <= k <= n
    let k: i32 = if mutation_kind == 7 {
        1i32                                                // k = 1 (first)
    } else if mutation_kind == 8 {
        n                                                   // k = n (last)
    } else if mutation_kind == 9 {
        (n + 1i32) / 2i32                                   // k = middle
    } else if mutation_kind == 10 && n >= 2 {
        2i32                                                // k = 2
    } else if mutation_kind == 11 && n >= 3 {
        n - 1                                               // k = n-1
    } else {
        // clamp seed_k to [1, n]
        if seed_k <= n {
            seed_k
        } else {
            n
        }
    };

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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
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
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 12;

    // Example test cases from description.md
    let examples: Vec<(i32, i32)> = vec![
        (13, 2),   // output: 10
        (1, 1),    // output: 1
    ];
    for &(n, k) in &examples {
        if seen.insert((n as i64, k as i64)) {
            let result = Solution::find_kth_number(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: interesting n values × k strategies
    let seed_ns: Vec<i32> = vec![
        1, 2, 3, 9, 10, 11, 13, 99, 100, 101, 999, 1000, 1001,
        9999, 10000, 100000, 999999, 1000000, 10000000,
        100000000, 999999999, 1000000000,
        12, 123, 1234, 12345, 123456, 1234567, 12345678, 123456789,
    ];

    let seed_ks: Vec<i32> = vec![
        1, 2, 3, 5, 10, 100, 1000, 10000, 100000, 1000000,
    ];

    // Seed pool × mutation_kind
    for &sn in &seed_ns {
        for &sk in &seed_ks {
            if sk > sn { continue; }
            for mk in 0..num_mutations {
                if count >= count_goal { break; }
                let (n, k) = generate_test_case(sn, sk, mk);
                if seen.insert((n as i64, k as i64)) {
                    let result = Solution::find_kth_number(n, k);
                    writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
                    count += 1;
                }
            }
            if count >= count_goal { break; }
        }
        if count >= count_goal { break; }
    }

    // Fill remaining with random seeds + random mutations across size classes
    while count < count_goal {
        let sn: i32 = match count % 5 {
            0 => rng.gen_range_i64(1, 10) as i32,                       // tiny
            1 => rng.gen_range_i64(1, 1000) as i32,                     // small
            2 => rng.gen_range_i64(1000, 100000) as i32,                // medium
            3 => rng.gen_range_i64(100000, 10000000) as i32,            // large
            _ => rng.gen_range_i64(10000000, 1000000000) as i32,        // max
        };
        let sk: i32 = rng.gen_range_i64(1, sn as i64) as i32;
        let mk = rng.gen_u8() % num_mutations;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n as i64, k as i64)) {
            let result = Solution::find_kth_number(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
