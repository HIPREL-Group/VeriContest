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
}

// Linear-time fib computation for proof use
pub open spec fn fib_pair(n: nat) -> (nat, nat)
    decreases n
{
    if n == 0 {
        (0nat, 1nat)
    } else {
        let p = fib_pair((n - 1) as nat);
        (p.1, p.0 + p.1)
    }
}

proof fn fib_pair_correct(n: nat)
    ensures
        fib_pair(n).0 == Solution::fib_spec(n),
        fib_pair(n).1 == Solution::fib_spec((n + 1) as nat),
    decreases n
{
    if n == 0 {
    } else {
        fib_pair_correct((n - 1) as nat);
        assert(Solution::fib_spec((n + 1) as nat)
            == Solution::fib_spec((n - 1) as nat) + Solution::fib_spec(n));
    }
}

proof fn fib_46_bound()
    ensures Solution::fib_spec(46nat) <= i32::MAX
{
    fib_pair_correct(46nat);
    assert(fib_pair(46nat).0 <= 2_147_483_647int) by(compute_only);
}

proof fn fib_bound_for_range(n: int)
    requires 1 <= n <= 45
    ensures Solution::fib_spec((n + 1) as nat) <= i32::MAX
{
    Solution::fib_is_monotonic((n + 1) as nat, 46nat);
    fib_46_bound();
}

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1i32 <= seed <= 45i32,
    ensures
        1 <= result <= 45,
        Solution::fib_spec((result + 1) as nat) <= i32::MAX,
{
    let r: i32 = if mutation_kind == 0 {
        seed                                        // identity
    } else if mutation_kind == 1 && seed < 45 {
        seed + 1                                    // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                    // nudge down
    } else if mutation_kind == 3 {
        1i32                                        // min boundary
    } else if mutation_kind == 4 {
        45i32                                       // max boundary
    } else if mutation_kind == 5 {
        23i32                                       // midpoint
    } else if mutation_kind == 6 {
        let half = seed / 2;
        if half >= 1 { half } else { 1i32 }         // halve
    } else if mutation_kind == 7 {
        if seed >= 1 && seed <= 22 {
            seed * 2                                // double
        } else {
            seed
        }
    } else if mutation_kind == 8 {
        2i32                                        // near-min
    } else if mutation_kind == 9 {
        44i32                                       // near-max
    } else {
        seed                                        // fallback
    };

    proof {
        fib_bound_for_range(r as int);
    }

    r
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
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
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![2, 3];
    for &n in &examples {
        if seen.insert(n) {
            let output = Solution::climb_stairs(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }

    // Seed pool: boundary values, powers of 2, interesting points
    let seed_pool: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        15, 20, 22, 23, 25, 30, 35, 40, 44, 45,
        11, 12, 16, 32,
    ];

    // Iterate seed pool × mutation kinds
    for &s in &seed_pool {
        for mk in 0..=10u8 {
            if generated >= count { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let output = Solution::climb_stairs(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random seeds and mutations
    let mut _attempts_0 = 0usize;
    while generated < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let s = rng.gen_range_i64(1, 45) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let output = Solution::climb_stairs(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            generated += 1;
        }
    }
}
