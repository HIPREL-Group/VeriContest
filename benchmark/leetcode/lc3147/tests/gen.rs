use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, fill_val: i32, corner_val: i32, k: i32, mutation_kind: u8) -> (energy: Vec<i32>)
    requires
        2 <= n <= 100_000,
        -1000 <= fill_val <= 1000,
        -1000 <= corner_val <= 1000,
        1 <= k <= n - 1,
    ensures
        1 <= energy.len() <= 100_000,
        forall |i: int| 0 <= i < energy.len() ==> -1000 <= #[trigger] energy[i] <= 1000,
        1 <= k <= energy.len() - 1,
{
    // Determine the mutated value for position 0
    let v0: i32 = if mutation_kind == 0 {
        fill_val                               // identity
    } else if mutation_kind == 1 {
        -1000                                  // min boundary
    } else if mutation_kind == 2 {
        1000                                   // max boundary
    } else if mutation_kind == 3 {
        0                                      // zero
    } else if mutation_kind == 4 && fill_val < 1000 {
        (fill_val + 1) as i32                  // nudge up
    } else if mutation_kind == 5 && fill_val > -1000 {
        (fill_val - 1) as i32                  // nudge down
    } else if mutation_kind == 6 {
        corner_val                             // use corner_val parameter
    } else if mutation_kind == 7 {
        1                                      // positive
    } else if mutation_kind == 8 {
        -1                                     // negative
    } else {
        fill_val                               // fallback
    };

    let mut energy: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            2 <= n <= 100_000,
            -1000 <= fill_val <= 1000,
            -1000 <= v0 <= 1000,
            energy.len() == idx,
            forall|j: int| 0 <= j < idx ==> -1000 <= #[trigger] energy[j] <= 1000,
        decreases n - idx,
    {
        if idx == 0 {
            energy.push(v0);
        } else {
            energy.push(fill_val);
        }
        idx += 1;
    }
    energy
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

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3147);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |energy: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}:{}", energy, k);
        if !seen.insert(key) { return; }
        let output = Solution::maximum_energy(energy.clone(), k);
        writeln!(out, "{}", json!({"input": {"energy": energy, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from problem description
    emit(vec![5, 2, -10, -5, 1], 3, &mut seen, &mut out, &mut count);
    emit(vec![-2, -3, -1], 2, &mut seen, &mut out, &mut count);

    // Generated inputs with mutations
    let fill_vals: Vec<i32> = vec![0, -1000, 1000, -1, 1, 500, -500, 999, -999];
    let corner_vals: Vec<i32> = vec![0, -1000, 1000, -1, 1, -500, 500];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];
    let sizes: Vec<usize> = vec![2, 3, 5, 10, 50, 100, 1000];

    for &n in &sizes {
        for &fv in &fill_vals {
            for &mk in &mutation_kinds {
                if count >= target { break; }
                let cv = corner_vals[mk as usize % corner_vals.len()];
                let k = ((n - 1).min(3)).max(1) as i32;
                let energy = generate_test_case(n, fv, cv, k, mk);
                emit(energy, k, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random inputs for extra diversity
    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),         // tiny
            1 => rng.gen_range_usize(2, 20),         // small
            2 => rng.gen_range_usize(20, 200),       // medium
            3 => rng.gen_range_usize(200, 1000),     // large
            _ => rng.gen_range_usize(1000, 10000),   // max
        };
        let k = rng.gen_range_usize(1, n - 1) as i32;
        let fill_val = rng.gen_range_i64(-1000, 1000) as i32;
        let corner_val = rng.gen_range_i64(-1000, 1000) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        let energy = generate_test_case(n, fill_val, corner_val, k, mk);
        emit(energy, k, &mut seen, &mut out, &mut count);
    }
}
