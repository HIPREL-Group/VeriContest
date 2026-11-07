use vstd::prelude::*;

verus! {

pub fn generate_test_case(mat: Vec<Vec<i32>>, k: i32, mutation_kind: u8) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= mat.len() <= 100,
        1 <= mat[0].len() <= 100,
        forall |i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
        forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==>
            1 <= #[trigger] mat[i][j] <= 100,
        1 <= k <= 100,
    ensures
        1 <= result.0.len() <= 100,
        1 <= result.0[0].len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == result.0[0].len(),
        forall |i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[0].len() ==>
            1 <= #[trigger] result.0[i][j] <= 100,
        1 <= result.1 <= 100,
{
    if mutation_kind == 0 {
        // identity
        (mat, k)
    } else if mutation_kind == 1 {
        // k = 1
        (mat, 1)
    } else if mutation_kind == 2 {
        // k = 100
        (mat, 100)
    } else if mutation_kind == 3 && k < 100 {
        // nudge k up
        (mat, k + 1)
    } else if mutation_kind == 4 && k > 1 {
        // nudge k down
        (mat, k - 1)
    } else if mutation_kind == 5 {
        // k = number of rows (covers all rows)
        let nk = mat.len() as i32;
        (mat, nk)
    } else if mutation_kind == 6 {
        // halve k
        let new_k = k / 2;
        (mat, if new_k >= 1 { new_k } else { 1 })
    } else if mutation_kind == 7 {
        // k = number of columns (covers all columns)
        let nk = mat[0].len() as i32;
        (mat, nk)
    } else {
        // fallback: identity
        (mat, k)
    }
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_matrix(rng: &mut Rng, m: usize, n: usize) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_i64(1, 100) as i32);
        }
        mat.push(row);
    }
    mat
}

fn all_val_matrix(m: usize, n: usize, val: i32) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(m);
    for _ in 0..m {
        mat.push(vec![val; n]);
    }
    mat
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1314);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |mat: Vec<Vec<i32>>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}:{}", mat, k);
        if !seen.insert(key) { return; }
        let output = Solution::matrix_block_sum(mat.clone(), k);
        writeln!(out, "{}", json!({"input": {"mat": mat, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let ex1_mat = vec![vec![1,2,3], vec![4,5,6], vec![7,8,9]];
    emit(ex1_mat.clone(), 1, &mut seen, &mut out, &mut count);
    emit(ex1_mat.clone(), 2, &mut seen, &mut out, &mut count);

    // Structured seed matrices with all mutation kinds
    let seed_matrices: Vec<(Vec<Vec<i32>>, i32)> = vec![
        // 1x1
        (vec![vec![1]], 1),
        (vec![vec![100]], 1),
        (vec![vec![50]], 100),
        // 1xN
        (vec![vec![1, 2, 3, 4, 5]], 1),
        (vec![vec![1, 2, 3, 4, 5]], 2),
        // Mx1
        (vec![vec![10], vec![20], vec![30]], 1),
        (vec![vec![10], vec![20], vec![30]], 3),
        // Small square
        (vec![vec![1, 1], vec![1, 1]], 1),
        (all_val_matrix(3, 3, 100), 1),
        (all_val_matrix(3, 3, 1), 3),
        // Rectangular
        (vec![vec![1, 2, 3, 4], vec![5, 6, 7, 8]], 1),
        (vec![vec![1, 2], vec![3, 4], vec![5, 6], vec![7, 8]], 2),
    ];

    let mutation_kinds: Vec<u8> = (0..=8).collect();

    for (mat, k) in &seed_matrices {
        for &mk in &mutation_kinds {
            let (result_mat, result_k) = generate_test_case(mat.clone(), *k, mk);
            emit(result_mat, result_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random matrices across size classes
    let mut _attempts_0 = 0usize;
    while count < target_count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let (m, n) = match count % 6 {
            0 => (1, 1),                                                  // 1x1
            1 => (rng.gen_range_usize(1, 3), rng.gen_range_usize(1, 3)), // tiny
            2 => (rng.gen_range_usize(2, 10), rng.gen_range_usize(2, 10)), // small
            3 => (rng.gen_range_usize(5, 30), rng.gen_range_usize(5, 30)), // medium
            4 => (rng.gen_range_usize(10, 60), rng.gen_range_usize(10, 60)), // large
            _ => (rng.gen_range_usize(50, 100), rng.gen_range_usize(50, 100)), // max
        };

        let mat = if count % 10 == 0 {
            all_val_matrix(m, n, 1)
        } else if count % 10 == 5 {
            all_val_matrix(m, n, 100)
        } else {
            random_matrix(&mut rng, m, n)
        };

        // k diversity: boundary and random
        let k = match count % 5 {
            0 => 1,
            1 => 100,
            2 => m.min(n) as i32,
            3 => rng.gen_range_i64(1, 100) as i32,
            _ => rng.gen_range_i64(1, m.max(n) as i64) as i32,
        };

        let mk = rng.gen_range_usize(0, 8) as u8;
        let (result_mat, result_k) = generate_test_case(mat, k, mk);
        emit(result_mat, result_k, &mut seen, &mut out, &mut count);
    }
}
