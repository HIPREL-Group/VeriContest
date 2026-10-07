use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn fib_spec(n: nat) -> nat
        decreases n
    {
        if n <= 0 {
            0
        } else if n == 1 {
            1
        } else {
            Solution::fib_spec((n - 2) as nat) + Solution::fib_spec((n - 1) as nat)
        }
    }

    proof fn fib_is_monotonic(i: nat, j: nat)
        requires
            i <= j,
        ensures
            Solution::fib_spec(i) <= Solution::fib_spec(j),
        decreases j - i,
    {
        if j < 2 {
        } else if i == j {
        } else if i == j - 1 {
        } else {
            Solution::fib_is_monotonic(i, (j - 1) as nat);
            Solution::fib_is_monotonic(i, (j - 2) as nat);
        }
    }

    proof fn fib_30_bound()
        ensures
            Solution::fib_spec(30) <= 832040,
    {
        reveal_with_fuel(Solution::fib_spec, 32);
    }
}

proof fn fib_spec_bound(n: nat)
    requires
        n <= 30,
    ensures
        Solution::fib_spec(n as nat) <= i32::MAX as nat,
{
    Solution::fib_30_bound();
    Solution::fib_is_monotonic(n, 30);
}

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0 <= seed <= 30,
    ensures
        0 <= result <= 30,
        Solution::fib_spec(result as nat) <= i32::MAX,
{
    let n: i32;
    if mutation_kind == 0 {
        n = seed;
    } else if mutation_kind == 1 && seed < 30 {
        n = seed + 1;
    } else if mutation_kind == 2 && seed > 0 {
        n = seed - 1;
    } else if mutation_kind == 3 && seed >= 0 && seed <= 15 {
        n = seed * 2;
    } else if mutation_kind == 4 {
        n = seed / 2;
    } else if mutation_kind == 5 {
        n = 0;
    } else if mutation_kind == 6 {
        n = 30;
    } else if mutation_kind == 7 {
        n = 0;
    } else {
        n = seed;
    }

    proof {
        fib_spec_bound(n as nat);
    }

    n
}

} // verus!

extern crate serde_json;
use serde_json::json;

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
    let mut generated = 0;
    let num_mutations: u8 = 8;

    // Example inputs from description
    let examples: Vec<i32> = vec![2, 3, 4];
    for n in &examples {
        if generated >= count { break; }
        if seen.insert(*n) {
            let result = Solution::fib(*n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            generated += 1;
        }
    }

    // Seed pool: all values 0..=30 with mutations
    let seeds: Vec<i32> = vec![
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        15, 20, 25, 28, 29, 30,
    ];

    for &s in &seeds {
        for mk in 0..num_mutations {
            if generated >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let result = Solution::fib(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
                generated += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    let mut _attempts_0 = 0usize;
    while generated < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let s = rng.gen_range_i64(0, 30) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let result = Solution::fib(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            generated += 1;
        }
    }
}
