use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_vals: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= seed_vals.len() <= 500_000,
    ensures
        1 <= result.len() <= 500_000,
{
    if mutation_kind == 0 {
        // identity
        seed_vals
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut v = seed_vals;
        v.set(0, 0);
        v
    } else if mutation_kind == 2 {
        // set last element to i32::MAX
        let mut v = seed_vals;
        let last = v.len() - 1;
        v.set(last, i32::MAX);
        v
    } else if mutation_kind == 3 && seed_vals.len() < 500_000 {
        // grow by one element
        let mut v = seed_vals;
        v.push(0);
        v
    } else if mutation_kind == 4 && seed_vals.len() > 1 {
        // shrink by one element
        let mut v = seed_vals;
        v.pop();
        v
    } else if mutation_kind == 5 {
        // set first element to i32::MIN
        let mut v = seed_vals;
        v.set(0, i32::MIN);
        v
    } else if mutation_kind == 6 && seed_vals.len() >= 2 {
        // swap first and last elements
        let mut v = seed_vals;
        let last = v.len() - 1;
        let first_val = v[0];
        let last_val = v[last];
        v.set(0, last_val);
        v.set(last, first_val);
        v
    } else if mutation_kind == 7 {
        // nudge first element up (if < MAX)
        let mut v = seed_vals;
        if v[0] < i32::MAX {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 8 {
        // nudge last element down (if > MIN)
        let mut v = seed_vals;
        let last = v.len() - 1;
        if v[last] > i32::MIN {
            v.set(last, v[last] - 1);
        }
        v
    } else if mutation_kind == 9 {
        // set all elements to the same value (no triplet possible)
        let val = seed_vals[0];
        let len = seed_vals.len();
        let mut v: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                v.len() == i,
                1 <= len <= 500_000,
            decreases len - i,
        {
            v.push(val);
            i += 1;
        }
        v
    } else {
        // fallback: identity
        seed_vals
    }
}

} // verus!

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

fn random_vec(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo, hi) as i32);
    }
    v
}

fn increasing_vec(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    let mut cur: i64 = rng.gen_range_i64(-1_000_000, 0);
    for _ in 0..len {
        v.push(cur as i32);
        cur += rng.gen_range_i64(1, 100);
        if cur > i32::MAX as i64 { cur = i32::MAX as i64; }
    }
    v
}

fn decreasing_vec(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    let mut cur: i64 = rng.gen_range_i64(0, 1_000_000);
    for _ in 0..len {
        v.push(cur as i32);
        cur -= rng.gen_range_i64(1, 100);
        if cur < i32::MIN as i64 { cur = i32::MIN as i64; }
    }
    v
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(334);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::increasing_triplet(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![2, 1, 5, 0, 4, 6],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds for diversity
    let crafted: Vec<Vec<i32>> = vec![
        vec![1],                              // single element
        vec![1, 2],                           // two elements
        vec![1, 2, 3],                        // minimal triplet
        vec![3, 2, 1],                        // no triplet, descending
        vec![1, 1, 1, 1, 1],                  // all same
        vec![i32::MIN, 0, i32::MAX],          // boundary triplet
        vec![i32::MAX, i32::MIN],             // boundary pair
        vec![0, 0, 0],                        // all zeros
        vec![-1, 0, 1],                       // negative to positive
        vec![1, 0, -1, 2, 3],                 // triplet after dip
        vec![5, 1, 5, 5, 2, 5, 4],            // subtle triplet (1,2,4)
        vec![20, 100, 10, 12, 5, 13],         // triplet (10,12,13)
    ];

    let mutation_kinds: Vec<u8> = (0..=9).collect();
    for seed_v in &crafted {
        for &mk in &mutation_kinds {
            let result = generate_test_case(seed_v.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with all mutation kinds
    while count < target_count {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),          // tiny
            1 => rng.gen_range_usize(1, 20),          // small
            2 => rng.gen_range_usize(21, 200),        // medium
            3 => rng.gen_range_usize(201, 2000),      // large
            _ => rng.gen_range_usize(2001, 10000),    // very large
        };

        // Vary value distribution
        let seed_v = match count % 4 {
            0 => random_vec(&mut rng, n, i32::MIN as i64, i32::MAX as i64),
            1 => random_vec(&mut rng, n, -100, 100),
            2 => increasing_vec(&mut rng, n),
            _ => decreasing_vec(&mut rng, n),
        };

        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_test_case(seed_v, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
