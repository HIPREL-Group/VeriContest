use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_val: usize,
    l_val: i32,
    r_delta: i32,
    mutation_kind: u8,
) -> (result: (usize, i32, i32))
    requires
        1 <= n_val <= 100_000,
        1 <= l_val <= 1_000_000_000i32,
        0 <= r_delta <= 1_000_000_000i32 - l_val,
    ensures
        1 <= result.0 <= 100_000,
        1 <= result.1 <= result.2 <= 1_000_000_000,
{
    let l = l_val;
    let r = l_val + r_delta;
    let mut n = n_val;

    if mutation_kind == 1 {
        // min n
        n = 1;
    } else if mutation_kind == 2 {
        // max n (capped at 100_000)
        n = 100_000;
    } else if mutation_kind == 3 {
        // n = 2
        n = 2;
    } else if mutation_kind == 4 {
        // nudge n down (min 1)
        if n > 1 {
            n = n - 1;
        }
    } else if mutation_kind == 5 {
        // nudge n up (max 100_000)
        if n < 100_000 {
            n = n + 1;
        }
    }

    (n, l, r)
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
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    let mut emit = |n: usize, l: i32, r: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{}_{}_{}", n, l, r);
        if !seen.insert(key) { return; }
        let (ok, a) = Solution::construct_gcd_array(n, l, r);
        let output: serde_json::Value = if ok {
            json!({"feasible": true, "array": a})
        } else {
            json!({"feasible": false, "array": []})
        };
        writeln!(out, "{}", json!({"input": {"n": n, "l": l, "r": r}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(5, 1, 5, &mut seen, &mut out, &mut count);
    emit(9, 1000, 2000, &mut seen, &mut out, &mut count);
    emit(10, 30, 35, &mut seen, &mut out, &mut count);
    emit(1, 1_000_000_000, 1_000_000_000, &mut seen, &mut out, &mut count);

    // Handcrafted boundary cases
    let seeds: Vec<(usize, i32, i32)> = vec![
        (1, 1, 0),
        (1, 1, 999_999_999),
        (1, 500_000_000, 500_000_000),
        (2, 1, 0),
        (2, 1, 1),
        (5, 1, 0),
        (10, 1, 99),
        (100, 1, 999),
        (1000, 1, 999_999),
        (100_000, 1, 999_999_999),
    ];

    for &(n_val, l_val, r_delta) in &seeds {
        for &mk in &mutation_kinds {
            let (n, l, r) = generate_test_case(n_val, l_val, r_delta, mk);
            emit(n, l, r, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    while count < target {
        let n_val: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 50),
            2 => rng.gen_range_usize(51, 1000),
            3 => rng.gen_range_usize(1001, 50_000),
            _ => rng.gen_range_usize(50_001, 100_000),
        };

        let l_val: i32 = match count % 4 {
            0 => 1,
            1 => rng.gen_range_i64(1, 1_000) as i32,
            2 => rng.gen_range_i64(1, 1_000_000) as i32,
            _ => rng.gen_range_i64(1, 1_000_000_000) as i32,
        };

        let max_delta = 1_000_000_000i64 - l_val as i64;
        let r_delta: i32 = if max_delta <= 0 {
            0
        } else {
            rng.gen_range_i64(0, max_delta) as i32
        };

        let mk = rng.gen_range_usize(0, 5) as u8;
        let (n, l, r) = generate_test_case(n_val, l_val, r_delta, mk);
        emit(n, l, r, &mut seen, &mut out, &mut count);
    }
}
