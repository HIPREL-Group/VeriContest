use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: Vec<i64>,
    mutation_kind: u8,
) -> (result: Vec<i64>)
    requires
        1 <= vals.len() <= 200_000,
        forall|i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 200_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // Identity: return vals unchanged
        vals
    } else if mutation_kind == 1 {
        // Uniform: set all elements to vals[0]
        let v0 = vals[0];
        let n = vals.len();
        let mut out: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                n == vals.len(),
                1 <= n <= 200_000,
                0 <= v0 <= 1_000_000_000,
                out.len() == idx,
                idx <= n,
                forall|j: int| 0 <= j < idx as int ==> #[trigger] out[j] == v0,
                forall|j: int| 0 <= j < idx as int ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - idx,
        {
            out.push(v0);
            idx = idx + 1;
        }
        out
    } else if mutation_kind == 2 && vals.len() < 200_000 {
        // Grow: push 0
        let mut out = vals;
        out.push(0i64);
        out
    } else if mutation_kind == 3 && vals.len() > 1 {
        // Shrink: pop last element
        let mut out = vals;
        let _ = out.pop();
        out
    } else if mutation_kind == 4 {
        // Set last element to 0
        let mut out = vals;
        let last = out.len() - 1;
        out.set(last, 0i64);
        out
    } else if mutation_kind == 5 {
        // Set last element to max boundary
        let mut out = vals;
        let last = out.len() - 1;
        out.set(last, 1_000_000_000i64);
        out
    } else if mutation_kind == 6 {
        // Set first element to 0
        let mut out = vals;
        out.set(0, 0i64);
        out
    } else if mutation_kind == 7 {
        // Set first element to max boundary
        let mut out = vals;
        out.set(0, 1_000_000_000i64);
        out
    } else if mutation_kind == 8 {
        // All zeros
        let n = vals.len();
        let mut out: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                1 <= n <= 200_000,
                out.len() == idx,
                idx <= n,
                forall|j: int| 0 <= j < idx as int ==> #[trigger] out[j] == 0,
                forall|j: int| 0 <= j < idx as int ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - idx,
        {
            out.push(0i64);
            idx = idx + 1;
        }
        out
    } else if mutation_kind == 9 {
        // All max
        let n = vals.len();
        let mut out: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                1 <= n <= 200_000,
                out.len() == idx,
                idx <= n,
                forall|j: int| 0 <= j < idx as int ==> #[trigger] out[j] == 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> 0 <= #[trigger] out[j] <= 1_000_000_000,
            decreases n - idx,
        {
            out.push(1_000_000_000i64);
            idx = idx + 1;
        }
        out
    } else {
        // Fallback: identity
        vals
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

    fn gen_range_u8(&mut self, lo: u8, hi: u8) -> u8 {
        let range = (hi as u16 - lo as u16 + 1) as u64;
        (lo as u64 + self.next_u64() % range) as u8
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
    let mut written = 0;
    let num_mutations: u8 = 10;

    // Example inputs from description.md
    let examples: Vec<Vec<i64>> = vec![
        vec![1],                // single element -> 0 ops
        vec![4, 6],             // diff=2, ops=2
        vec![2, 1, 2, 1, 2, 1], // diff=1, ops=1
        vec![20, 32],           // diff=12, ops=6
    ];

    // Emit examples first
    for a in &examples {
        if written >= count { break; }
        let result = Solution::min_operations(a.clone());
        writeln!(out, "{}", json!({
            "input": {"a": a},
            "output": result
        })).unwrap();
        written += 1;
    }

    // Boundary and interesting seed arrays with all mutations
    let boundary_arrays: Vec<Vec<i64>> = vec![
        vec![0],
        vec![1_000_000_000],
        vec![0, 1_000_000_000],
        vec![0, 0, 0],
        vec![1_000_000_000, 1_000_000_000],
        vec![0, 500_000_000, 1_000_000_000],
        vec![1, 2, 3, 4, 5],
    ];

    for arr in &boundary_arrays {
        for mk in 0..num_mutations {
            if written >= count { break; }
            let result_arr = generate_test_case(arr.clone(), mk);
            let result = Solution::min_operations(result_arr.clone());
            writeln!(out, "{}", json!({
                "input": {"a": result_arr},
                "output": result
            })).unwrap();
            written += 1;
        }
    }

    // Random test cases with diverse sizes
    while written < count {
        let n: usize = match written % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 5000),   // big
        };

        let mut vals: Vec<i64> = Vec::with_capacity(n);
        for _ in 0..n {
            let v = if written % 5 == 0 {
                // Boundary values ~20% of the time
                match rng.gen_range_u8(0, 4) {
                    0 => 0,
                    1 => 1_000_000_000,
                    2 => 1,
                    3 => 999_999_999,
                    _ => rng.gen_range_i64(0, 1_000_000_000),
                }
            } else {
                rng.gen_range_i64(0, 1_000_000_000)
            };
            vals.push(v);
        }

        let mk = rng.gen_range_u8(0, num_mutations - 1);
        let result_arr = generate_test_case(vals, mk);
        let result = Solution::min_operations(result_arr.clone());
        writeln!(out, "{}", json!({
            "input": {"a": result_arr},
            "output": result
        })).unwrap();
        written += 1;
    }

    eprintln!("Generated {} test cases", written);
}
