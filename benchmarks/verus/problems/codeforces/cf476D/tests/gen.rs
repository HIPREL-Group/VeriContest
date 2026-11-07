use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, seed_k: i32, mutation_kind: u8)
    -> (result: (usize, i32))
    requires
        1 <= seed_n <= 10000,
        1 <= seed_k <= 100,
    ensures
        1 <= result.0 <= 10000,
        1 <= result.1 <= 100,
{
    let mut n = seed_n;
    let mut k = seed_k;

    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 && n < 10000 {
        n = n + 1;                           // nudge n up
    } else if mutation_kind == 2 && n > 1 {
        n = n - 1;                           // nudge n down
    } else if mutation_kind == 3 && k < 100 {
        k = k + 1;                           // nudge k up
    } else if mutation_kind == 4 && k > 1 {
        k = k - 1;                           // nudge k down
    } else if mutation_kind == 5 {
        n = 1;                               // min n
    } else if mutation_kind == 6 {
        n = 10000;                           // max n
    } else if mutation_kind == 7 {
        k = 1;                               // min k
    } else if mutation_kind == 8 {
        k = 100;                             // max k
    } else if mutation_kind == 9 {
        n = 1;
        k = 1;                               // both min
    } else if mutation_kind == 10 {
        n = 10000;
        k = 100;                             // both max
    } else if mutation_kind == 11 && n <= 5000 {
        n = n * 2;                           // double n
    } else if mutation_kind == 12 {
        n = n / 2 + 1;                       // halve n (stay >= 1)
    } else if mutation_kind == 13 && k <= 50 {
        k = k * 2;                           // double k
    } else if mutation_kind == 14 {
        k = k / 2 + 1;                       // halve k (stay >= 1)
    } else {
        // fallback: identity
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let range = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % range) as i64) as i32
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    use std::io::Write;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    // Example 1 from description.md: n=1, k=1
    {
        let n: usize = 1;
        let k: i32 = 1;
        let sets = Solution::build_dreamoon_sets(n, k);
        writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": sets})).unwrap();
    }
    // Example 2 from description.md: n=2, k=2
    {
        let n: usize = 2;
        let k: i32 = 2;
        let sets = Solution::build_dreamoon_sets(n, k);
        writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": sets})).unwrap();
    }

    let num_mutations: u8 = 15;
    let mut generated: usize = 2; // already wrote examples

    while generated < count {
        let (seed_n, seed_k) = match generated % 5 {
            0 => {
                // tiny values
                let n = rng.gen_range_usize(1, 5);
                let k = rng.gen_range_i32(1, 5);
                (n, k)
            }
            1 => {
                // small values
                let n = rng.gen_range_usize(1, 100);
                let k = rng.gen_range_i32(1, 20);
                (n, k)
            }
            2 => {
                // medium values
                let n = rng.gen_range_usize(100, 1000);
                let k = rng.gen_range_i32(1, 50);
                (n, k)
            }
            3 => {
                // large values
                let n = rng.gen_range_usize(1000, 10000);
                let k = rng.gen_range_i32(50, 100);
                (n, k)
            }
            _ => {
                // boundary values
                let n_boundaries: [usize; 5] = [1, 2, 5000, 9999, 10000];
                let k_boundaries: [i32; 5] = [1, 2, 50, 99, 100];
                let n = n_boundaries[(rng.next_u64() as usize) % 5];
                let k = k_boundaries[(rng.next_u64() as usize) % 5];
                (n, k)
            }
        };

        let mutation_kind = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k) = generate_test_case(seed_n, seed_k, mutation_kind);
        let sets = Solution::build_dreamoon_sets(n, k);
        writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": sets})).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
