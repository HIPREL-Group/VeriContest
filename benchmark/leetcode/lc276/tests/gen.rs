use vstd::prelude::*;

verus! {

pub open spec fn paint_ways(n: int, k: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else if n == 1 {
        k
    } else if n == 2 {
        k * k
    } else {
        (k - 1) * (paint_ways(n - 1, k) + paint_ways(n - 2, k))
    }
}

proof fn paint_ways_k1_bounded(n: int)
    requires 0 <= n
    ensures paint_ways(n, 1) <= i32::MAX as int
    decreases n
{
    if n <= 0 {
    } else if n == 1 {
    } else if n == 2 {
    } else {
        paint_ways_k1_bounded(n - 1);
        paint_ways_k1_bounded(n - 2);
    }
}

pub fn generate_test_case(seed_n: u8, seed_k: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        0 <= seed_n <= 50,
        1 <= seed_k <= 100000,
    ensures
        0 <= res.0 <= 50,
        1 <= res.1 <= 100000,
        paint_ways(res.0 as int, res.1 as int) <= i32::MAX as int,
{
    if mutation_kind % 4 == 0 {
        let k = if mutation_kind == 0 {
            seed_k
        } else if mutation_kind == 4 && seed_k < 100000 {
            seed_k + 1
        } else if mutation_kind == 8 && seed_k > 1 {
            seed_k - 1
        } else if mutation_kind == 12 {
            1i32
        } else if mutation_kind == 16 {
            100000i32
        } else {
            seed_k
        };
        (0, k)
    } else if mutation_kind % 4 == 1 {
        let k = if mutation_kind == 1 {
            seed_k
        } else if mutation_kind == 5 && seed_k < 100000 {
            seed_k + 1
        } else if mutation_kind == 9 && seed_k > 1 {
            seed_k - 1
        } else if mutation_kind == 13 {
            1i32
        } else if mutation_kind == 17 {
            100000i32
        } else {
            seed_k
        };
        (1, k)
    } else if mutation_kind % 4 == 2 {
        let k_raw = if seed_k <= 46340 { seed_k } else { 1 + ((seed_k - 1) % 46340) };
        let k = if mutation_kind == 2 {
            k_raw
        } else if mutation_kind == 6 && k_raw < 46340 {
            k_raw + 1
        } else if mutation_kind == 10 && k_raw > 1 {
            k_raw - 1
        } else if mutation_kind == 14 {
            1i32
        } else if mutation_kind == 18 {
            46340i32
        } else {
            k_raw
        };
        assert(1 <= k <= 46340);
        assert(k as int * k as int <= 46340int * 46340int) by(nonlinear_arith)
            requires 1 <= k as int <= 46340int;
        assert(46340int * 46340int <= i32::MAX as int);
        (2, k)
    } else {
        let n: i32 = if mutation_kind == 3 {
            seed_n as i32
        } else if mutation_kind == 7 && seed_n < 50 {
            (seed_n + 1) as i32
        } else if mutation_kind == 11 && seed_n > 0 {
            (seed_n - 1) as i32
        } else if mutation_kind == 15 {
            0i32
        } else if mutation_kind == 19 {
            50i32
        } else if mutation_kind == 23 {
            25i32
        } else {
            seed_n as i32
        };
        proof { paint_ways_k1_bounded(n as int); }
        (n, 1)
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

mod code_impl {
    pub struct Solution;
    include!("../code.rs");
}

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
    let mut generated = 0;
    let num_mutations: u8 = 24;

    let examples: Vec<(i32, i32)> = vec![(3, 2), (1, 1)];

    for &(n, k) in &examples {
        if generated >= count { break; }
        if seen.insert((n, k)) {
            let result = code_impl::Solution::num_ways(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            generated += 1;
        }
    }

    let seed_ns: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 10, 15, 20, 25, 30, 35, 40, 45, 50];
    let seed_ks: Vec<i32> = vec![1, 2, 3, 5, 10, 100, 1000, 10000, 46340, 100000];

    for &sn in &seed_ns {
        for &sk in &seed_ks {
            for mk in 0..num_mutations {
                if generated >= count { break; }
                let (n, k) = generate_test_case(sn, sk, mk);
                if seen.insert((n, k)) {
                    let result = code_impl::Solution::num_ways(n, k);
                    writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
                    generated += 1;
                }
            }
        }
    }

    while generated < count {
        let sn = rng.gen_range_i64(0, 50) as u8;
        let sk = rng.gen_range_i64(1, 100000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k) = generate_test_case(sn, sk, mk);
        if seen.insert((n, k)) {
            let result = code_impl::Solution::num_ways(n, k);
            writeln!(out, "{}", json!({"input": {"n": n, "k": k}, "output": result})).unwrap();
            generated += 1;
        }
    }
}
