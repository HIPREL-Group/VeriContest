use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10000,
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 100000 { 100000usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 10000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > 10000 { 10000 } else { value };
        result.push(value);
        i += 1;
    }
    result
}

pub fn generate_test_case(arr: Vec<i32>, k: i32, threshold: i32) -> (result: (Vec<i32>, i32, i32))
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000,
        1 <= result.1 <= result.0.len(),
        0 <= result.2 <= 10000,
{
    let arr = bounded_values(&arr);
    let k = if k < 1 { 1 } else if k as usize > arr.len() { arr.len() as i32 } else { k };
    let threshold = if threshold < 0 { 0 } else if threshold > 10000 { 10000 } else { threshold };
    (arr, k, threshold)
}


pub fn generate_candidate(
    arr: Vec<i32>,
    k_val: i32,
    threshold_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= arr.len() <= 100_000,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 10_000,
        1 <= k_val,
        k_val as usize <= arr.len(),
        0 <= threshold_val <= 10_000,
    ensures
        1 <= result.0.len(),
        result.0.len() <= 100_000,
        1 <= result.1,
        result.1 as usize <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 10_000,
        0 <= result.2,
        result.2 <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        (arr, k_val, threshold_val)
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 0);
        (a, k_val, threshold_val)
    } else if mutation_kind == 2 {
        // set last element to 10_000
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 10_000);
        (a, k_val, threshold_val)
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> a[j] == 0i32,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 0);
            i += 1;
        }
        (a, k_val, threshold_val)
    } else if mutation_kind == 4 {
        // set all elements to 10_000
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> a[j] == 10_000i32,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 10_000);
            i += 1;
        }
        (a, k_val, threshold_val)
    } else if mutation_kind == 5 {
        // set threshold to 0
        (arr, k_val, 0i32)
    } else if mutation_kind == 6 {
        // set threshold to 10_000
        (arr, k_val, 10_000i32)
    } else if mutation_kind == 7 {
        // set k to 1
        (arr, 1i32, threshold_val)
    } else if mutation_kind == 8 {
        // set k to arr.len()
        let k = arr.len() as i32;
        (arr, k, threshold_val)
    } else if mutation_kind == 9 && arr.len() < 100_000 {
        // grow by one element (push 0)
        let mut a = arr;
        a.push(0);
        (a, k_val, threshold_val)
    } else if mutation_kind == 10 && arr.len() > 1 && (k_val as usize) < arr.len() {
        // shrink by one element (pop)
        let mut a = arr;
        a.pop();
        (a, k_val, threshold_val)
    } else {
        // fallback: identity
        (arr, k_val, threshold_val)
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

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 10_000) as i32);
    }
    v
}

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
    let mut total = 0usize;

    let mut emit = |arr: Vec<i32>, k: i32, threshold: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        let (arr, k, threshold) = generate_test_case(arr, k, threshold);
        if *total >= count { return; }
        let key = format!("{:?}:{}:{}", arr, k, threshold);
        if !seen.insert(key) { return; }
        let result = Solution::num_of_subarrays(arr.clone(), k, threshold);
        writeln!(out, "{}", json!({
            "input": {"arr": arr, "k": k, "threshold": threshold},
            "output": result
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![2, 2, 2, 2, 5, 5, 5, 8], 3, 4),
        (vec![11, 13, 17, 23, 29, 31, 7, 5, 2, 3], 3, 5),
    ];
    for (arr, k, threshold) in examples {
        emit(arr, k, threshold, &mut seen, &mut out, &mut total);
    }

    // Edge case seeds
    let edge_seeds: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![0], 1, 0),
        (vec![10_000], 1, 10_000),
        (vec![10_000], 1, 0),
        (vec![0], 1, 10_000),
        (vec![0, 0, 0], 1, 0),
        (vec![0, 0, 0], 3, 0),
        (vec![10_000, 10_000, 10_000], 3, 10_000),
        (vec![10_000, 10_000, 10_000], 1, 10_000),
        (vec![1, 2, 3, 4, 5], 2, 3),
        (vec![1, 2, 3, 4, 5], 5, 3),
        (vec![5000, 5000, 5000, 5000, 5000], 3, 5000),
        (vec![1, 1, 1, 1, 1], 1, 1),
        (vec![1, 1, 1, 1, 1], 1, 2),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply every mutation to every edge seed
    for (arr, k, threshold) in &edge_seeds {
        for &mk in &mutation_kinds {
            let (a, k_out, t_out) = generate_candidate(arr.clone(), *k, *threshold, mk);
            emit(a, k_out, t_out, &mut seen, &mut out, &mut total);
        }
    }

    // Random test cases with diverse sizes
    while total < count {
        let n: usize = match total % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 20),        // small
            2 => rng.gen_range_usize(21, 200),      // medium
            3 => rng.gen_range_usize(201, 5000),    // large
            _ => rng.gen_range_usize(5001, 100_000), // max
        };
        let arr = random_arr(&mut rng, n);
        let k = rng.gen_range_i64(1, n as i64) as i32;
        let threshold = rng.gen_range_i64(0, 10_000) as i32;
        let mk = rng.gen_range_usize(0, 10) as u8;
        let (a, k_out, t_out) = generate_candidate(arr, k, threshold, mk);
        emit(a, k_out, t_out, &mut seen, &mut out, &mut total);
    }
}
