use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: Vec<i32>,
    rows: usize,
    cols: usize,
    r: i32,
    c: i32,
    mutation_kind: u8,
) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= rows <= 100,
        1 <= cols <= 100,
        1 <= r <= 300,
        1 <= c <= 300,
        values.len() == rows * cols,
        rows * cols <= 10_000,
        forall|i: int| 0 <= i < values.len() ==> -1_000 <= #[trigger] values[i] <= 1_000,
    ensures
        1 <= mat.len() <= 100,
        1 <= mat[0].len() <= 100,
        1 <= r <= 300,
        1 <= c <= 300,
        forall |k: int| 0 <= k < mat.len() ==> #[trigger] mat[k].len() == mat[0].len(),
        forall |i:int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==> -1_000 <= #[trigger] mat[i][j] <= 1_000,
        mat.len() * mat[0].len() <= usize::MAX,
        r * c <= usize::MAX,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut row_idx: usize = 0;

    while row_idx < rows
        invariant
            0 <= row_idx <= rows,
            mat.len() == row_idx as int,
            1 <= rows <= 100,
            1 <= cols <= 100,
            values.len() == rows * cols,
            rows * cols <= 10_000,
            forall|i: int| 0 <= i < values.len() ==> -1_000 <= #[trigger] values[i] <= 1_000,
            forall|k: int| 0 <= k < row_idx as int ==> (#[trigger] mat[k]).len() == cols as int,
            forall|k: int, j: int| 0 <= k < row_idx as int && 0 <= j < cols as int
                ==> -1_000 <= #[trigger] mat[k][j] <= 1_000,
        decreases rows - row_idx,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut col_idx: usize = 0;

        while col_idx < cols
            invariant
                0 <= col_idx <= cols,
                row.len() == col_idx as int,
                1 <= cols <= 100,
                1 <= rows <= 100,
                values.len() == rows * cols,
                rows * cols <= 10_000,
                row_idx < rows,
                forall|i: int| 0 <= i < values.len() ==> -1_000 <= #[trigger] values[i] <= 1_000,
                forall|j: int| 0 <= j < col_idx as int ==> -1_000 <= #[trigger] row[j] <= 1_000,
            decreases cols - col_idx,
        {
            assert(row_idx * cols + col_idx < values.len()) by(nonlinear_arith)
                requires
                    row_idx < rows,
                    col_idx < cols,
                    values.len() == rows * cols,
                    rows >= 1,
                    cols >= 1,
            ;
            let flat_idx: usize = row_idx * cols + col_idx;

            let val: i32 = if mutation_kind == 1 {
                0i32
            } else if mutation_kind == 2 {
                -1000i32
            } else if mutation_kind == 3 {
                1000i32
            } else if mutation_kind == 4 {
                1i32
            } else if mutation_kind == 5 {
                -1i32
            } else if mutation_kind == 6 && values[flat_idx] > -1000 {
                (values[flat_idx] - 1) as i32
            } else if mutation_kind == 7 && values[flat_idx] < 1000 {
                (values[flat_idx] + 1) as i32
            } else if mutation_kind == 8 {
                if values[flat_idx] >= 0 {
                    values[flat_idx]
                } else {
                    (-values[flat_idx]) as i32
                }
            } else {
                values[flat_idx]
            };

            row.push(val);
            col_idx += 1;
        }

        mat.push(row);
        row_idx += 1;
    }

    assert(mat.len() == rows as int);
    assert(mat.len() >= 1);

    proof {
        // All rows have length cols, so mat[0].len() == cols
        assert(mat[0].len() == cols as int);
        // And all mat[k].len() == cols == mat[0].len()
        assert forall|k: int| 0 <= k < mat.len() implies (#[trigger] mat[k]).len() == mat[0].len() by {
            assert(mat[k].len() == cols as int);
            assert(mat[0].len() == cols as int);
        };
        assert(mat.len() * mat[0].len() <= usize::MAX) by(nonlinear_arith)
            requires
                mat.len() <= 100,
                mat[0].len() <= 100,
        ;
        assert((r as int) * (c as int) <= usize::MAX) by(nonlinear_arith)
            requires
                1 <= r <= 300,
                1 <= c <= 300,
        ;
    }

    mat
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

fn random_flat_values(rng: &mut Rng, count: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(count);
    for _ in 0..count {
        v.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    v
}

fn build_matrix(values: Vec<i32>, rows: usize, cols: usize, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(values, rows, cols, 1, 1, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(566);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n = 0usize;

    let mut emit = |mat: Vec<Vec<i32>>, r: i32, c: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    n: &mut usize| {
        if *n >= count { return; }
        let key = format!("{:?},{},{}", mat, r, c);
        if !seen.insert(key) { return; }
        let output = Solution::matrix_reshape(mat.clone(), r, c);
        writeln!(out, "{}", json!({
            "input": {"mat": mat, "r": r, "c": c},
            "output": output
        })).unwrap();
        *n += 1;
    };

    // Example 1: mat = [[1,2],[3,4]], r = 1, c = 4
    emit(vec![vec![1,2], vec![3,4]], 1, 4, &mut seen, &mut out, &mut n);
    // Example 2: mat = [[1,2],[3,4]], r = 2, c = 4 (invalid reshape)
    emit(vec![vec![1,2], vec![3,4]], 2, 4, &mut seen, &mut out, &mut n);

    // Hand-crafted edge cases
    // 1x1 matrix
    emit(vec![vec![0]], 1, 1, &mut seen, &mut out, &mut n);
    // 1x1 with boundary value
    emit(vec![vec![1000]], 1, 1, &mut seen, &mut out, &mut n);
    emit(vec![vec![-1000]], 1, 1, &mut seen, &mut out, &mut n);
    // 1x4 -> 2x2 (valid)
    emit(vec![vec![1,2,3,4]], 2, 2, &mut seen, &mut out, &mut n);
    // 2x2 -> 1x4 (valid)
    emit(vec![vec![1,2], vec![3,4]], 1, 4, &mut seen, &mut out, &mut n);
    // 2x3 -> 3x2 (valid)
    emit(vec![vec![1,2,3], vec![4,5,6]], 3, 2, &mut seen, &mut out, &mut n);
    // 2x3 -> 2x2 (invalid, 6 != 4)
    emit(vec![vec![1,2,3], vec![4,5,6]], 2, 2, &mut seen, &mut out, &mut n);

    // Size classes for rows/cols
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 1), (1, 2), (2, 1), (1, 100), (100, 1),
        (2, 2), (3, 3), (5, 5), (10, 10), (10, 5),
        (50, 2), (4, 25), (20, 5), (100, 100),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // For each size class, generate with various mutations and r,c combos
    for &(rows, cols) in &size_classes {
        let total = rows * cols;
        let base_values = random_flat_values(&mut rng, total);

        for &mk in &mutation_kinds {
            if n >= count { break; }
            let mat = build_matrix(base_values.clone(), rows, cols, mk);

            // Valid reshape: same total, different shape
            if total > 1 {
                // Try to find a valid (r, c) pair
                let r_val = if total <= 300 { 1i32 } else { rows as i32 };
                let c_val = if total <= 300 { total as i32 } else { cols as i32 };
                if 1 <= r_val && r_val <= 300 && 1 <= c_val && c_val <= 300 {
                    emit(mat.clone(), r_val, c_val, &mut seen, &mut out, &mut n);
                }
            }

            // Invalid reshape: r*c != rows*cols
            let bad_r = rows as i32;
            let bad_c = (cols as i32) + 1;
            if bad_c <= 300 {
                emit(mat.clone(), bad_r, bad_c, &mut seen, &mut out, &mut n);
            }

            // Same shape
            emit(mat, rows as i32, cols as i32, &mut seen, &mut out, &mut n);
        }
    }

    // Random cases
    while n < count {
        let rows = match n % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 30),
            3 => rng.gen_range_usize(30, 70),
            _ => rng.gen_range_usize(70, 100),
        };
        let max_cols = std::cmp::min(100, 10000 / rows);
        let cols = rng.gen_range_usize(1, max_cols);
        let total = rows * cols;
        let values = random_flat_values(&mut rng, total);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let mat = build_matrix(values, rows, cols, mk);

        // Randomly choose valid or invalid reshape
        if rng.next_u64() % 2 == 0 && total <= 300 {
            // Valid reshape
            let divisors: Vec<usize> = (1..=total).filter(|d| total % d == 0 && *d <= 300 && total / *d <= 300).collect();
            if !divisors.is_empty() {
                let r_val = divisors[rng.gen_range_usize(0, divisors.len() - 1)] as i32;
                let c_val = (total / r_val as usize) as i32;
                emit(mat, r_val, c_val, &mut seen, &mut out, &mut n);
                continue;
            }
        }
        // Invalid or same shape
        let r_val = rng.gen_range_usize(1, 300) as i32;
        let c_val = rng.gen_range_usize(1, 300) as i32;
        emit(mat, r_val, c_val, &mut seen, &mut out, &mut n);
    }
}
