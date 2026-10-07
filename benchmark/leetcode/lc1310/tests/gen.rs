use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    arr: Vec<i32>,
    queries: Vec<Vec<i32>>,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= arr.len() <= 30_000,
        1 <= queries.len() <= 30_000,
        forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1_000_000_000,
        forall|k: int|
            0 <= k < queries.len() ==> #[trigger] queries[k].len() == 2
                && 0 <= queries[k][0] <= queries[k][1] < arr.len() as i32,
    ensures
        1 <= result.0.len() <= 30_000,
        1 <= result.1.len() <= 30_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|k: int|
            0 <= k < result.1.len() ==> #[trigger] result.1[k].len() == 2
                && 0 <= result.1[k][0] <= result.1[k][1] < result.0.len() as i32,
{
    (arr, queries)
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    arr
}

fn random_queries(rng: &mut Rng, n: usize, num_queries: usize) -> Vec<Vec<i32>> {
    let mut queries = Vec::with_capacity(num_queries);
    for _ in 0..num_queries {
        let l = rng.gen_range_usize(0, n - 1) as i32;
        let r = rng.gen_range_usize(l as usize, n - 1) as i32;
        queries.push(vec![l, r]);
    }
    queries
}

fn apply_mutation(mut arr: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    if mutation_kind == 1 {
        for i in 0..arr.len() { arr[i] = 1; }
    } else if mutation_kind == 2 {
        arr[0] = 1_000_000_000;
    } else if mutation_kind == 3 {
        arr[0] = 1;
    } else if mutation_kind == 4 && arr[0] < 1_000_000_000 {
        arr[0] += 1;
    } else if mutation_kind == 5 && arr[0] > 1 {
        arr[0] -= 1;
    } else if mutation_kind == 6 && arr.len() > 1 {
        let last = arr.len() - 1;
        arr[last] = 1;
    } else if mutation_kind == 7 && arr.len() > 1 {
        let last = arr.len() - 1;
        arr[last] = 1_000_000_000;
    }
    arr
}

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1310);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut emitted = 0usize;

    let mut emit = |arr: Vec<i32>, queries_vec: Vec<Vec<i32>>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let output = Solution::xor_queries(arr.clone(), queries_vec.clone());
        writeln!(out, "{}", json!({
            "input": {"arr": arr, "queries": queries_vec},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example 1 from description
    emit(
        vec![1, 3, 4, 8],
        vec![vec![0, 1], vec![1, 2], vec![0, 3], vec![3, 3]],
        &mut out, &mut emitted,
    );
    // Example 2 from description
    emit(
        vec![4, 8, 2, 10],
        vec![vec![2, 3], vec![1, 3], vec![0, 0], vec![0, 3]],
        &mut out, &mut emitted,
    );

    // Size classes for arr length
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),         // tiny
        (5, 20),        // small
        (20, 100),      // medium
        (100, 1000),    // large
        (1000, 5000),   // big
    ];

    // Query count classes
    let query_classes: Vec<(usize, usize)> = vec![
        (1, 3),
        (3, 10),
        (10, 50),
        (50, 200),
        (200, 1000),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Systematic: each size class × query class × some mutations
    for &(arr_lo, arr_hi) in &size_classes {
        for &(q_lo, q_hi) in &query_classes {
            if emitted >= count { break; }
            let n = rng.gen_range_usize(arr_lo, arr_hi);
            let nq = rng.gen_range_usize(q_lo, q_hi);
            let arr = random_arr(&mut rng, n);
            let queries = random_queries(&mut rng, n, nq);
            let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
            let arr = apply_mutation(arr, mk);
            let (result_arr, result_queries) = generate_test_case(arr, queries);
            emit(result_arr, result_queries, &mut out, &mut emitted);
        }
    }

    // Edge cases: single element array
    for mk in 0..8u8 {
        if emitted >= count { break; }
        let arr = vec![rng.gen_range_i64(1, 1_000_000_000) as i32];
        let arr = apply_mutation(arr, mk);
        let queries = vec![vec![0, 0]];
        let (result_arr, result_queries) = generate_test_case(arr, queries);
        emit(result_arr, result_queries, &mut out, &mut emitted);
    }

    // Edge case: full-range query on each size
    for &(arr_lo, arr_hi) in &size_classes {
        if emitted >= count { break; }
        let n = rng.gen_range_usize(arr_lo, arr_hi);
        let arr = random_arr(&mut rng, n);
        let queries = vec![vec![0, (n - 1) as i32]];
        let (result_arr, result_queries) = generate_test_case(arr, queries);
        emit(result_arr, result_queries, &mut out, &mut emitted);
    }

    // Boundary values in arr
    for mk in 0..8u8 {
        if emitted >= count { break; }
        let arr = vec![1, 1_000_000_000, 1, 500_000_000];
        let arr = apply_mutation(arr, mk);
        let queries = vec![vec![0, 0], vec![0, 3], vec![1, 2], vec![2, 3], vec![3, 3]];
        let (result_arr, result_queries) = generate_test_case(arr, queries);
        emit(result_arr, result_queries, &mut out, &mut emitted);
    }

    // Fill remaining with random
    while emitted < count {
        let n = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 3000),
        };
        let nq = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let arr = random_arr(&mut rng, n);
        let queries = random_queries(&mut rng, n, nq);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let arr = apply_mutation(arr, mk);
        let (result_arr, result_queries) = generate_test_case(arr, queries);
        emit(result_arr, result_queries, &mut out, &mut emitted);
    }
}
