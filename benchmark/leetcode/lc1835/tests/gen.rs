use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    arr1: Vec<i32>,
    arr2: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= arr1.len() <= 100_000,
        1 <= arr2.len() <= 100_000,
        forall |i: int| 0 <= i < arr1.len() ==> 0 <= #[trigger] arr1[i] <= 1_000_000_000,
        forall |j: int| 0 <= j < arr2.len() ==> 0 <= #[trigger] arr2[j] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall |j: int| 0 <= j < result.1.len() ==> 0 <= #[trigger] result.1[j] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (arr1, arr2)
    } else if mutation_kind == 1 {
        // set first element of arr1 to 0 (min boundary)
        let mut a = arr1;
        a.set(0, 0);
        (a, arr2)
    } else if mutation_kind == 2 {
        // set first element of arr1 to max boundary
        let mut a = arr1;
        a.set(0, 1_000_000_000);
        (a, arr2)
    } else if mutation_kind == 3 {
        // set last element of arr1 to 0
        let mut a = arr1;
        let last = a.len() - 1;
        a.set(last, 0);
        (a, arr2)
    } else if mutation_kind == 4 {
        // set last element of arr1 to max boundary
        let mut a = arr1;
        let last = a.len() - 1;
        a.set(last, 1_000_000_000);
        (a, arr2)
    } else if mutation_kind == 5 {
        // set first element of arr2 to 0 (min boundary)
        let mut b = arr2;
        b.set(0, 0);
        (arr1, b)
    } else if mutation_kind == 6 {
        // set first element of arr2 to max boundary
        let mut b = arr2;
        b.set(0, 1_000_000_000);
        (arr1, b)
    } else if mutation_kind == 7 {
        // set last element of arr2 to 0
        let mut b = arr2;
        let last = b.len() - 1;
        b.set(last, 0);
        (arr1, b)
    } else if mutation_kind == 8 {
        // set last element of arr2 to max boundary
        let mut b = arr2;
        let last = b.len() - 1;
        b.set(last, 1_000_000_000);
        (arr1, b)
    } else if mutation_kind == 9 && arr1[0] < 1_000_000_000 {
        // nudge first element of arr1 up
        let mut a = arr1;
        let v = a[0] + 1;
        a.set(0, v);
        (a, arr2)
    } else if mutation_kind == 10 && arr1[0] > 0 {
        // nudge first element of arr1 down
        let mut a = arr1;
        let v = a[0] - 1;
        a.set(0, v);
        (a, arr2)
    } else if mutation_kind == 11 && arr2[0] < 1_000_000_000 {
        // nudge first element of arr2 up
        let mut b = arr2;
        let v = b[0] + 1;
        b.set(0, v);
        (arr1, b)
    } else if mutation_kind == 12 && arr2[0] > 0 {
        // nudge first element of arr2 down
        let mut b = arr2;
        let v = b[0] - 1;
        b.set(0, v);
        (arr1, b)
    } else if mutation_kind == 13 {
        // set all arr1 elements to 0
        let mut a = arr1;
        let mut k: usize = 0;
        while k < a.len()
            invariant
                a.len() == arr1.len(),
                a.len() <= 100_000,
                forall |i: int| 0 <= i < k as int ==> #[trigger] a[i] == 0,
                forall |i: int| k as int <= i < a.len() ==> 0 <= #[trigger] a[i] <= 1_000_000_000,
            decreases a.len() - k,
        {
            a.set(k, 0);
            k += 1;
        }
        (a, arr2)
    } else if mutation_kind == 14 {
        // set all arr2 elements to 0
        let mut b = arr2;
        let mut k: usize = 0;
        while k < b.len()
            invariant
                b.len() == arr2.len(),
                b.len() <= 100_000,
                forall |i: int| 0 <= i < k as int ==> #[trigger] b[i] == 0,
                forall |i: int| k as int <= i < b.len() ==> 0 <= #[trigger] b[i] <= 1_000_000_000,
            decreases b.len() - k,
        {
            b.set(k, 0);
            k += 1;
        }
        (arr1, b)
    } else if mutation_kind == 15 && arr1.len() >= 2 {
        // swap first two elements of arr1
        let mut a = arr1;
        let v0 = a[0];
        let v1 = a[1];
        a.set(0, v1);
        a.set(1, v0);
        (a, arr2)
    } else if mutation_kind == 16 && arr2.len() >= 2 {
        // swap first two elements of arr2
        let mut b = arr2;
        let v0 = b[0];
        let v1 = b[1];
        b.set(0, v1);
        b.set(1, v0);
        (arr1, b)
    } else {
        // fallback: identity
        (arr1, arr2)
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
    let mut count = 0;
    let num_mutations: u8 = 17;

    // Helper to generate a random array of given length with values in [0, 1_000_000_000]
    let gen_arr = |rng: &mut Rng, len: usize| -> Vec<i32> {
        (0..len).map(|_| rng.gen_range_i64(0, 1_000_000_000) as i32).collect()
    };

    // Example inputs from description
    let example_cases: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 2, 3], vec![6, 5]),
        (vec![12], vec![4]),
    ];

    for (a1, a2) in &example_cases {
        if count >= target { break; }
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (r1, r2) = generate_test_case(a1.clone(), a2.clone(), mk);
            let key = format!("{:?}|{:?}", r1, r2);
            if seen.insert(key) {
                let result = Solution::get_xor_sum(r1.clone(), r2.clone());
                writeln!(out, "{}", json!({"input": {"arr1": r1, "arr2": r2}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Boundary cases
    let boundary_cases: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![0], vec![0]),
        (vec![1_000_000_000], vec![1_000_000_000]),
        (vec![0], vec![1_000_000_000]),
        (vec![1_000_000_000], vec![0]),
        (vec![0, 0], vec![0, 0]),
        (vec![1, 1], vec![1, 1]),
    ];

    for (a1, a2) in &boundary_cases {
        if count >= target { break; }
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (r1, r2) = generate_test_case(a1.clone(), a2.clone(), mk);
            let key = format!("{:?}|{:?}", r1, r2);
            if seen.insert(key) {
                let result = Solution::get_xor_sum(r1.clone(), r2.clone());
                writeln!(out, "{}", json!({"input": {"arr1": r1, "arr2": r2}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Random cases with diverse size classes
    while count < target {
        let n1 = match rng.next_u64() % 5 {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 5000),  // very large
        };
        let n2 = match rng.next_u64() % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let a1 = gen_arr(&mut rng, n1);
        let a2 = gen_arr(&mut rng, n2);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (r1, r2) = generate_test_case(a1, a2, mk);
        let key = format!("{:?}|{:?}", r1, r2);
        if seen.insert(key) {
            let result = Solution::get_xor_sum(r1.clone(), r2.clone());
            writeln!(out, "{}", json!({"input": {"arr1": r1, "arr2": r2}, "output": result})).unwrap();
            count += 1;
        }
    }
}
