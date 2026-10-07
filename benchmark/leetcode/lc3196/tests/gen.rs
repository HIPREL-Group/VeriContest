use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seeds: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= seeds.len() <= 100000,
        forall|i: int| 0 <= i < seeds.len() ==> -1000000000 <= #[trigger] seeds[i] <= 1000000000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> -1000000000 <= #[trigger] result[i] <= 1000000000,
{
    if mutation_kind == 0 {
        seeds
    } else if mutation_kind == 1 && seeds.len() > 1 {
        let mut out = Vec::new();
        let target_len = seeds.len() - 1;
        let mut j: usize = 0;
        while j < target_len
            invariant
                0 <= j <= target_len,
                target_len == seeds.len() - 1,
                target_len >= 1,
                out.len() == j,
                forall|k: int| 0 <= k < j as int ==> -1000000000 <= #[trigger] out[k] <= 1000000000,
                1 <= seeds.len() <= 100000,
                forall|i: int| 0 <= i < seeds.len() ==> -1000000000 <= #[trigger] seeds[i] <= 1000000000,
            decreases target_len - j,
        {
            out.push(seeds[j]);
            j += 1;
        }
        out
    } else if mutation_kind == 2 && seeds.len() < 100000 {
        let mut out = Vec::new();
        let mut j: usize = 0;
        while j < seeds.len()
            invariant
                0 <= j <= seeds.len(),
                out.len() == j,
                forall|k: int| 0 <= k < j as int ==> -1000000000 <= #[trigger] out[k] <= 1000000000,
                1 <= seeds.len() <= 100000,
                seeds.len() < 100000,
                forall|i: int| 0 <= i < seeds.len() ==> -1000000000 <= #[trigger] seeds[i] <= 1000000000,
            decreases seeds.len() - j,
        {
            out.push(seeds[j]);
            j += 1;
        }
        out.push(0i32);
        out
    } else if mutation_kind == 3 {
        let mut out = Vec::new();
        let mut j: usize = 0;
        while j < seeds.len()
            invariant
                0 <= j <= seeds.len(),
                out.len() == j,
                forall|k: int| 0 <= k < j as int ==> -1000000000 <= #[trigger] out[k] <= 1000000000,
                1 <= seeds.len() <= 100000,
                forall|i: int| 0 <= i < seeds.len() ==> -1000000000 <= #[trigger] seeds[i] <= 1000000000,
            decreases seeds.len() - j,
        {
            let v = seeds[j];
            if v == -1000000000 {
                out.push(1000000000i32);
            } else {
                out.push(-v);
            }
            j += 1;
        }
        out
    } else if mutation_kind == 4 {
        let mut out = Vec::new();
        let mut j: usize = 0;
        while j < seeds.len()
            invariant
                0 <= j <= seeds.len(),
                out.len() == j,
                forall|k: int| 0 <= k < j as int ==> -1000000000 <= #[trigger] out[k] <= 1000000000,
                1 <= seeds.len() <= 100000,
            decreases seeds.len() - j,
        {
            out.push(0i32);
            j += 1;
        }
        out
    } else if mutation_kind == 5 {
        let mut out = Vec::new();
        let mut j: usize = 0;
        while j < seeds.len()
            invariant
                0 <= j <= seeds.len(),
                out.len() == j,
                forall|k: int| 0 <= k < j as int ==> -1000000000 <= #[trigger] out[k] <= 1000000000,
                1 <= seeds.len() <= 100000,
            decreases seeds.len() - j,
        {
            out.push(1000000000i32);
            j += 1;
        }
        out
    } else if mutation_kind == 6 {
        let mut out = Vec::new();
        let mut j: usize = 0;
        while j < seeds.len()
            invariant
                0 <= j <= seeds.len(),
                out.len() == j,
                forall|k: int| 0 <= k < j as int ==> -1000000000 <= #[trigger] out[k] <= 1000000000,
                1 <= seeds.len() <= 100000,
            decreases seeds.len() - j,
        {
            out.push(-1000000000i32);
            j += 1;
        }
        out
    } else if mutation_kind == 7 && seeds.len() >= 2 {
        let mut out = Vec::new();
        let mut j: usize = 0;
        while j < seeds.len()
            invariant
                0 <= j <= seeds.len(),
                out.len() == j,
                forall|k: int| 0 <= k < j as int ==> -1000000000 <= #[trigger] out[k] <= 1000000000,
                seeds.len() >= 2,
                1 <= seeds.len() <= 100000,
                forall|i: int| 0 <= i < seeds.len() ==> -1000000000 <= #[trigger] seeds[i] <= 1000000000,
            decreases seeds.len() - j,
        {
            if j == 0 {
                out.push(seeds[1]);
            } else if j == 1 {
                out.push(seeds[0]);
            } else {
                out.push(seeds[j]);
            }
            j += 1;
        }
        out
    } else if mutation_kind == 8 {
        let mut out = Vec::new();
        let mut j: usize = 0;
        while j < seeds.len()
            invariant
                0 <= j <= seeds.len(),
                out.len() == j,
                forall|k: int| 0 <= k < j as int ==> -1000000000 <= #[trigger] out[k] <= 1000000000,
                1 <= seeds.len() <= 100000,
                forall|i: int| 0 <= i < seeds.len() ==> -1000000000 <= #[trigger] seeds[i] <= 1000000000,
            decreases seeds.len() - j,
        {
            if j == 0 && seeds[0] < 1000000000 {
                out.push(seeds[0] + 1);
            } else {
                out.push(seeds[j]);
            }
            j += 1;
        }
        out
    } else {
        seeds
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
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut rng = Rng::new(seed);

    let examples: Vec<Vec<i32>> = vec![
        vec![1, -2, 3, 4],
        vec![1, -1, 1, -1],
        vec![0],
        vec![1, -1],
    ];

    for nums in &examples {
        let result = Solution::maximum_total_cost(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();
    }

    let num_mutations: u8 = 9;
    let remaining = if count > examples.len() { count - examples.len() } else { 0 };

    for i in 0..remaining {
        let n: usize = match i % 6 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(2, 20),
            3 => rng.gen_range_usize(21, 500),
            4 => rng.gen_range_usize(501, 10000),
            _ => rng.gen_range_usize(10001, 100000),
        };

        let mut seeds: Vec<i32> = Vec::with_capacity(n);
        for j in 0..n {
            let val = if j % 5 == 0 {
                match rng.gen_range_usize(0, 4) {
                    0 => -1000000000i32,
                    1 => 1000000000i32,
                    2 => 0i32,
                    3 => 1i32,
                    _ => -1i32,
                }
            } else {
                rng.gen_range_i64(-1000000000, 1000000000) as i32
            };
            seeds.push(val);
        }

        let mutation_kind = (i % num_mutations as usize) as u8;
        let nums = generate_test_case(seeds, mutation_kind);
        let result = Solution::maximum_total_cost(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();
    }
}
