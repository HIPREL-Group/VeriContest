use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, target: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= arr.len() <= 10_000,
        forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000,
        1 <= target <= 100_000,
    ensures
        1 <= result.0.len() <= 10_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        1 <= result.1 <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (arr, target)
    } else if mutation_kind == 1 && target < 100_000 {
        // nudge target up
        (arr, target + 1)
    } else if mutation_kind == 2 && target > 1 {
        // nudge target down
        (arr, target - 1)
    } else if mutation_kind == 3 {
        // target = 1 (min boundary)
        (arr, 1)
    } else if mutation_kind == 4 {
        // target = 100_000 (max boundary)
        (arr, 100_000)
    } else if mutation_kind == 5 {
        // set last element to 1 (min element)
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 1);
        (a, target)
    } else if mutation_kind == 6 {
        // set last element to 100_000 (max element)
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 100_000);
        (a, target)
    } else if mutation_kind == 7 {
        // set all elements to 1
        let mut a = arr;
        let n = a.len();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == a.len(),
                1 <= n <= 10_000,
                forall|k: int| #![trigger a[k]] 0 <= k < j ==> a[k] == 1i32,
                forall|k: int| #![trigger a[k]] j <= k < n ==> 1 <= a[k] && a[k] <= 100_000,
            decreases n - j,
        {
            a.set(j, 1);
            j += 1;
        }
        (a, target)
    } else if mutation_kind == 8 && arr.len() < 10_000 {
        // grow: push element 1
        let mut a = arr;
        a.push(1);
        (a, target)
    } else if mutation_kind == 9 && arr.len() > 1 {
        // shrink: pop last element
        let mut a = arr;
        a.pop();
        (a, target)
    } else if mutation_kind == 10 {
        // nudge first element up if < 100_000
        let mut a = arr;
        if a[0] < 100_000 {
            a.set(0, a[0] + 1);
        }
        (a, target)
    } else if mutation_kind == 11 {
        // nudge first element down if > 1
        let mut a = arr;
        if a[0] > 1 {
            a.set(0, a[0] - 1);
        }
        (a, target)
    } else {
        // fallback
        (arr, target)
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

extern crate serde_json;
use serde_json::json;

fn random_arr(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, target: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal { return; }
        let key = format!("{:?}_{}", arr, target);
        if !seen.insert(key) { return; }
        let result = Solution::find_best_value(arr.clone(), target);
        writeln!(out, "{}", json!({"input": {"arr": arr, "target": target}, "output": result})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![4, 9, 3], 10),
        (vec![2, 3, 5], 10),
        (vec![60864, 25176, 27249, 21296, 20204], 56803),
    ];
    for (arr, target) in examples {
        emit(arr, target, &mut seen, &mut out, &mut count);
    }

    // Seed inputs with various mutations
    let seed_arrs: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![100_000], 100_000),
        (vec![1], 100_000),
        (vec![100_000], 1),
        (vec![1, 1, 1], 3),
        (vec![50_000, 50_000], 100_000),
        (vec![1, 2, 3, 4, 5], 15),
        (vec![1, 2, 3, 4, 5], 1),
        (vec![10, 20, 30], 50),
        (vec![99_999, 99_998, 99_997], 100_000),
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();
    for (arr, target) in &seed_arrs {
        for &mk in &mutation_kinds {
            let (ra, rt) = generate_test_case(arr.clone(), *target, mk);
            emit(ra, rt, &mut seen, &mut out, &mut count);
        }
    }

    // Size classes for random generation
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),       // tiny
        (4, 10),      // small
        (11, 100),    // medium
        (101, 1000),  // large
        (1001, 5000), // big
    ];

    // Random test cases with mutations
    for i in 0..200 {
        if count >= goal { break; }
        let (lo_n, hi_n) = size_classes[i % size_classes.len()];
        let n = rng.gen_range_usize(lo_n, hi_n);

        // Vary value ranges
        let (val_lo, val_hi): (i32, i32) = match i % 4 {
            0 => (1, 100),
            1 => (1, 10_000),
            2 => (1, 100_000),
            _ => (50_000, 100_000),
        };

        let arr = random_arr(&mut rng, n, val_lo, val_hi);
        let target = rng.gen_range_i64(1, 100_000) as i32;
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (ra, rt) = generate_test_case(arr, target, mk);
        emit(ra, rt, &mut seen, &mut out, &mut count);
    }

    // Fill remainder with identity mutation
    while count < goal {
        let n = rng.gen_range_usize(1, 1000);
        let arr = random_arr(&mut rng, n, 1, 100_000);
        let target = rng.gen_range_i64(1, 100_000) as i32;
        let (ra, rt) = generate_test_case(arr, target, 0);
        emit(ra, rt, &mut seen, &mut out, &mut count);
    }
}
