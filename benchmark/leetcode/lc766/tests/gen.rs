use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    row_vals: Vec<i32>,
    mutation_kind: u8,
) -> (matrix: Vec<Vec<i32>>)
    requires
        1 <= rows <= 20,
        1 <= cols <= 20,
        row_vals.len() == rows,
        forall |k: int| 0 <= k < row_vals.len() ==> 0 <= #[trigger] row_vals[k] <= 99,
    ensures
        1 <= matrix.len() <= 20,
        forall |i: int| 0 <= i < matrix.len() ==> 1 <= #[trigger] matrix[i].len() <= 20,
        forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
        forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[0].len() ==> 0 <= #[trigger] matrix[i][j] <= 99,
{
    let eff_rows: usize = if mutation_kind == 6 {
        1
    } else {
        rows
    };
    let eff_cols: usize = if mutation_kind == 7 {
        1
    } else {
        cols
    };

    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < eff_rows
        invariant
            0 <= i <= eff_rows,
            matrix.len() == i,
            1 <= eff_rows <= 20,
            1 <= eff_cols <= 20,
            0 <= mutation_kind,
            row_vals.len() == rows,
            1 <= rows <= 20,
            eff_rows <= rows,
            forall |k: int| 0 <= k < row_vals.len() ==> 0 <= #[trigger] row_vals[k] <= 99,
            forall |k: int| 0 <= k < i as int ==> #[trigger] matrix[k].len() == eff_cols,
            forall |k: int, l: int| 0 <= k < i as int && 0 <= l < eff_cols as int
                ==> 0 <= #[trigger] matrix[k][l] <= 99,
        decreases eff_rows - i,
    {
        let val: i32 = if mutation_kind == 1 {
            0i32
        } else if mutation_kind == 2 {
            99i32
        } else if mutation_kind == 3 {
            50i32
        } else if mutation_kind == 4 && row_vals[i] < 99 {
            (row_vals[i] + 1) as i32
        } else if mutation_kind == 5 && row_vals[i] > 0 {
            (row_vals[i] - 1) as i32
        } else if mutation_kind == 8 {
            row_vals[0]
        } else {
            row_vals[i]
        };

        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < eff_cols
            invariant
                0 <= j <= eff_cols,
                row.len() == j,
                0 <= val <= 99,
                forall |l: int| 0 <= l < j as int ==> 0 <= #[trigger] row[l] <= 99,
            decreases eff_cols - j,
        {
            row.push(val);
            j = j + 1;
        }
        matrix.push(row);
        i = i + 1;
    }
    matrix
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

fn build_matrix(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    let mut matrix = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for _ in 0..cols {
            row.push(rng.gen_range_i64(0, 99) as i32);
        }
        matrix.push(row);
    }
    matrix
}

fn make_toeplitz_matrix(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    // A Toeplitz matrix is defined by its first row and first column
    let mut first_row = Vec::with_capacity(cols);
    for _ in 0..cols {
        first_row.push(rng.gen_range_i64(0, 99) as i32);
    }
    let mut first_col = Vec::with_capacity(rows);
    first_col.push(first_row[0]);
    for _ in 1..rows {
        first_col.push(rng.gen_range_i64(0, 99) as i32);
    }
    let mut matrix = Vec::with_capacity(rows);
    for i in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for j in 0..cols {
            if j >= i {
                row.push(first_row[j - i]);
            } else {
                row.push(first_col[i - j]);
            }
        }
        matrix.push(row);
    }
    matrix
}

fn gen_row_vals(rng: &mut Rng, rows: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(rows);
    for _ in 0..rows {
        v.push(rng.gen_range_i64(0, 99) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(766);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |matrix: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}", matrix);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::is_toeplitz_matrix(matrix.clone());
        writeln!(
            out,
            "{}",
            json!({"input": {"matrix": matrix}, "output": output})
        )
        .unwrap();
        *emitted += 1;
    };

    // Example inputs from description
    emit(
        vec![vec![1, 2, 3, 4], vec![5, 1, 2, 3], vec![9, 5, 1, 2]],
        &mut seen, &mut out, &mut emitted,
    );
    emit(
        vec![vec![1, 2], vec![2, 2]],
        &mut seen, &mut out, &mut emitted,
    );

    // Boundary: 1x1 matrix
    emit(vec![vec![0]], &mut seen, &mut out, &mut emitted);
    emit(vec![vec![99]], &mut seen, &mut out, &mut emitted);

    // Boundary: single row
    emit(vec![vec![1, 2, 3]], &mut seen, &mut out, &mut emitted);

    // Boundary: single column
    emit(
        vec![vec![1], vec![2], vec![3]],
        &mut seen, &mut out, &mut emitted,
    );

    // 20x20 uniform (always Toeplitz)
    emit(vec![vec![42; 20]; 20], &mut seen, &mut out, &mut emitted);

    // Use verified generator with mutation kinds
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];
    for &mk in &mutation_kinds {
        for size_class in 0..5 {
            let (rows, cols) = match size_class {
                0 => (1, 1),
                1 => (2, 2),
                2 => (rng.gen_range_usize(3, 10), rng.gen_range_usize(3, 10)),
                3 => (rng.gen_range_usize(10, 20), rng.gen_range_usize(10, 20)),
                _ => (20, 20),
            };
            let row_vals = gen_row_vals(&mut rng, rows);
            let matrix = generate_test_case(rows, cols, row_vals, mk);
            emit(matrix, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random Toeplitz matrices (always true)
    for _ in 0..15 {
        let rows = rng.gen_range_usize(1, 20);
        let cols = rng.gen_range_usize(1, 20);
        let matrix = make_toeplitz_matrix(&mut rng, rows, cols);
        emit(matrix, &mut seen, &mut out, &mut emitted);
    }

    // Random non-uniform matrices (may or may not be Toeplitz)
    while emitted < count {
        let rows = rng.gen_range_usize(1, 20);
        let cols = rng.gen_range_usize(1, 20);
        let matrix = build_matrix(&mut rng, rows, cols);
        emit(matrix, &mut seen, &mut out, &mut emitted);
    }
}
