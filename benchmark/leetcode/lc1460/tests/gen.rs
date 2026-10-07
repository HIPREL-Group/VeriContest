use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    fill_val: i32,
    alt_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 1000,
        1 <= fill_val <= 1000,
        1 <= alt_val <= 1000,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 1000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1000,
{
    let mut target: Vec<i32> = Vec::new();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 1000,
            1 <= fill_val <= 1000,
            1 <= alt_val <= 1000,
            target.len() == i,
            arr.len() == i,
            forall |j: int| 0 <= j < target.len() ==> 1 <= #[trigger] target[j] <= 1000,
            forall |j: int| 0 <= j < arr.len() ==> 1 <= #[trigger] arr[j] <= 1000,
        decreases n - i,
    {
        let tv: i32;
        let av: i32;

        if mutation_kind == 0 {
            // Both arrays identical (uniform fill_val)
            tv = fill_val;
            av = fill_val;
        } else if mutation_kind == 1 {
            // target all fill_val, arr all alt_val
            tv = fill_val;
            av = alt_val;
        } else if mutation_kind == 2 {
            // Both arrays alternating fill_val/alt_val (same multiset)
            tv = if i % 2 == 0 { fill_val } else { alt_val };
            av = if i % 2 == 0 { fill_val } else { alt_val };
        } else if mutation_kind == 3 {
            // target: first half fill, second half alt
            // arr: first half alt, second half fill (swapped halves)
            tv = if i < n / 2 { fill_val } else { alt_val };
            av = if i < n / 2 { alt_val } else { fill_val };
        } else if mutation_kind == 4 {
            // target all fill_val, arr same except last is alt_val
            tv = fill_val;
            av = if i == n - 1 { alt_val } else { fill_val };
        } else if mutation_kind == 5 {
            // target: first is alt_val rest fill_val
            // arr: last is alt_val rest fill_val (same multiset)
            tv = if i == 0 { alt_val } else { fill_val };
            av = if i == n - 1 { alt_val } else { fill_val };
        } else if mutation_kind == 6 {
            // Both arrays uniform alt_val
            tv = alt_val;
            av = alt_val;
        } else if mutation_kind == 7 {
            // Checkerboard: target alternating, arr reverse alternating
            tv = if i % 2 == 0 { fill_val } else { alt_val };
            av = if i % 2 == 0 { alt_val } else { fill_val };
        } else {
            // Fallback: both uniform fill_val
            tv = fill_val;
            av = fill_val;
        };

        target.push(tv);
        arr.push(av);
        i += 1;
    }
    (target, arr)
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |target: Vec<i32>,
                    arr: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}|{:?}", target, arr);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::can_be_equal(target.clone(), arr.clone());
        writeln!(out, "{}", json!({
            "input": {"target": target, "arr": arr},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example 1 from description.md
    emit(
        vec![1, 2, 3, 4], vec![2, 4, 1, 3],
        &mut seen, &mut out, &mut count,
    );
    // Example 2
    emit(
        vec![7], vec![7],
        &mut seen, &mut out, &mut count,
    );
    // Example 3
    emit(
        vec![3, 7, 9], vec![3, 7, 11],
        &mut seen, &mut out, &mut count,
    );

    // Size classes
    let sizes: Vec<usize> = vec![
        1, 2, 3, 4, 5, 10, 20, 50, 100, 200, 500, 1000,
    ];
    // Boundary fill values
    let fill_pairs: Vec<(i32, i32)> = vec![
        (1, 1), (1, 1000), (1000, 1), (1000, 1000),
        (500, 500), (1, 2), (999, 1000), (500, 501),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Systematic: size × fill_pair × mutation_kind
    for &n in &sizes {
        for &(fv, av) in &fill_pairs {
            for &mk in &mutation_kinds {
                if count >= count_target { break; }
                let (target, arr) = generate_test_case(n, fv, av, mk);
                emit(target, arr, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random test cases to fill remaining
    while count < count_target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),     // tiny
            1 => rng.gen_range_usize(6, 20),     // small
            2 => rng.gen_range_usize(21, 100),   // medium
            3 => rng.gen_range_usize(101, 500),  // large
            _ => rng.gen_range_usize(501, 1000), // max
        };
        let fill_val = rng.gen_range_i64(1, 1000) as i32;
        let alt_val = rng.gen_range_i64(1, 1000) as i32;
        let mk = rng.gen_range_usize(0, 7) as u8;

        let (mut target, mut arr) = generate_test_case(n, fill_val, alt_val, mk);

        // Randomly overwrite some elements for extra diversity (unverified but valid)
        let num_overwrites = rng.gen_range_usize(0, n / 4 + 1);
        for _ in 0..num_overwrites {
            let idx = rng.gen_range_usize(0, n - 1);
            let v = rng.gen_range_i64(1, 1000) as i32;
            if rng.gen_range_usize(0, 1) == 0 {
                target[idx] = v;
            } else {
                arr[idx] = v;
            }
        }

        emit(target, arr, &mut seen, &mut out, &mut count);
    }
}
