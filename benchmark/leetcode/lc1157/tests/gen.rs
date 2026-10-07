use vstd::prelude::*;

verus! {

pub struct Gen {
    pub arr: Vec<i32>,
}

impl Gen {
    pub fn generate_test_case(
        &self,
        left_seed: i32,
        right_seed: i32,
        mutation_kind: u8,
    ) -> (result: (i32, i32, i32))
        requires
            1 <= self.arr.len() <= 20_000,
            forall |i: int| 0 <= i < self.arr@.len() ==> 1 <= #[trigger] self.arr@[i] <= 20_000,
            0 <= left_seed <= right_seed,
            right_seed < self.arr.len() as i32,
        ensures
            1 <= self.arr.len() <= 20_000,
            forall |i: int| 0 <= i < self.arr@.len() ==> 1 <= #[trigger] self.arr@[i] <= 20_000,
            0 <= result.0 <= result.1,
            result.1 < self.arr.len() as i32,
            result.2 >= 1,
            result.2 <= result.1 - result.0 + 1,
            2 * result.2 > result.1 - result.0 + 1,
    {
        let left = left_seed;
        let right = right_seed;
        let span = right - left + 1;
        let min_thresh = span / 2 + 1;

        let threshold = if mutation_kind == 0 {
            // minimum valid threshold
            min_thresh
        } else if mutation_kind == 1 {
            // maximum valid threshold (= span)
            span
        } else if mutation_kind == 2 && min_thresh < span {
            // one above minimum
            min_thresh + 1
        } else if mutation_kind == 3 && span >= 2 && span - 1 >= min_thresh {
            // one below maximum
            span - 1
        } else if mutation_kind == 4 {
            min_thresh
        } else {
            // fallback: minimum threshold
            min_thresh
        };

        (left, right, threshold)
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

include!("../code.rs");

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i64(1, 20_000) as i32).collect()
}

fn random_arr_with_majority(rng: &mut Rng, len: usize, left: usize, right: usize) -> Vec<i32> {
    // Build an array where the subarray [left..right] has a clear majority element
    let span = right - left + 1;
    let majority_val = rng.gen_range_i64(1, 20_000) as i32;
    let majority_count = span / 2 + 1; // guarantees majority
    let mut arr: Vec<i32> = (0..len).map(|_| rng.gen_range_i64(1, 20_000) as i32).collect();
    // Place majority element in the subarray
    for i in 0..majority_count {
        arr[left + i] = majority_val;
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1157);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |arr: &Vec<i32>, left: i32, right: i32, threshold: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}_{}_{}_{}", arr, left, right, threshold);
        if !seen.insert(key) {
            return;
        }
        let checker = MajorityChecker::new(arr.clone());
        let output = checker.query(left, right, threshold);
        writeln!(out, "{}", json!({
            "input": {"arr": arr, "left": left, "right": right, "threshold": threshold},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example test cases from description.md
    {
        let arr = vec![1, 1, 2, 2, 1, 1];
        emit(&arr, 0, 5, 4, &mut seen, &mut out, &mut total);
        emit(&arr, 0, 3, 3, &mut seen, &mut out, &mut total);
        emit(&arr, 2, 3, 2, &mut seen, &mut out, &mut total);
    }

    // Edge cases: single element
    {
        let arr = vec![1];
        emit(&arr, 0, 0, 1, &mut seen, &mut out, &mut total);
        let arr = vec![20_000];
        emit(&arr, 0, 0, 1, &mut seen, &mut out, &mut total);
    }

    // Edge case: all same elements
    {
        let arr = vec![5; 10];
        emit(&arr, 0, 9, 6, &mut seen, &mut out, &mut total);
        emit(&arr, 3, 7, 3, &mut seen, &mut out, &mut total);
    }

    // Edge case: no majority
    {
        let arr: Vec<i32> = (1..=10).collect();
        emit(&arr, 0, 9, 6, &mut seen, &mut out, &mut total);
    }

    // Diverse test cases using the verified generator
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),       // tiny
        (6, 20),      // small
        (21, 100),    // medium
        (101, 1000),  // large
        (1001, 5000), // big
        (5001, 20000),// max
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    for (lo, hi) in &size_classes {
        for &mk in &mutation_kinds {
            if total >= count { break; }
            let n = rng.gen_range_usize(*lo, *hi);
            let left_idx = rng.gen_range_usize(0, n - 1);
            let right_idx = rng.gen_range_usize(left_idx, n - 1);

            // Sometimes create arrays with a clear majority
            let arr = if mk % 2 == 0 {
                random_arr_with_majority(&mut rng, n, left_idx, right_idx)
            } else {
                random_arr(&mut rng, n)
            };

            let gen = Gen { arr: arr.clone() };
            let (left, right, threshold) = gen.generate_test_case(
                left_idx as i32, right_idx as i32, mk
            );
            emit(&arr, left, right, threshold, &mut seen, &mut out, &mut total);
        }
    }

    // Fill remaining with random cases
    while total < count {
        let n = match total % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 20),
            2 => rng.gen_range_usize(1, 100),
            3 => rng.gen_range_usize(1, 1000),
            _ => rng.gen_range_usize(1, 20_000),
        };
        let left_idx = rng.gen_range_usize(0, n - 1);
        let right_idx = rng.gen_range_usize(left_idx, n - 1);

        let arr = if rng.next_u64() % 3 == 0 {
            random_arr_with_majority(&mut rng, n, left_idx, right_idx)
        } else {
            random_arr(&mut rng, n)
        };

        let mk = (rng.next_u64() % 5) as u8;
        let gen = Gen { arr: arr.clone() };
        let (left, right, threshold) = gen.generate_test_case(
            left_idx as i32, right_idx as i32, mk
        );
        emit(&arr, left, right, threshold, &mut seen, &mut out, &mut total);
    }

    eprintln!("Generated {} test cases", total);
}
