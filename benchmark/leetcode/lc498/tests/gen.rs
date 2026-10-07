use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    num_rows: usize,
    num_cols: usize,
    flat_values: Vec<i32>,
    mutation_kind: u8,
) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= num_rows <= 10_000,
        1 <= num_cols <= 10_000,
        num_rows * num_cols <= 10_000,
        flat_values.len() == num_rows * num_cols,
        forall|i: int| 0 <= i < flat_values.len() ==> -100_000 <= #[trigger] flat_values[i] <= 100_000,
    ensures
        1 <= mat.len() <= 10_000,
        1 <= mat[0].len() <= 10_000,
        forall|r: int| 0 <= r < mat.len() ==> #[trigger] mat[r].len() == mat[0].len(),
        forall|r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[0].len() ==> -100_000 <= #[trigger] mat[r][c] <= 100_000,
        mat.len() * mat[0].len() <= 10_000,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < num_rows
        invariant
            0 <= r <= num_rows,
            mat.len() == r,
            1 <= num_rows <= 10_000,
            1 <= num_cols <= 10_000,
            num_rows * num_cols <= 10_000,
            flat_values.len() == num_rows * num_cols,
            forall|i: int| 0 <= i < flat_values.len() ==> -100_000 <= #[trigger] flat_values[i] <= 100_000,
            forall|rr: int| 0 <= rr < r ==> (#[trigger] mat[rr]).len() == num_cols,
            forall|rr: int, cc: int| 0 <= rr < r && 0 <= cc < num_cols
                ==> -100_000 <= #[trigger] mat[rr][cc] <= 100_000,
        decreases num_rows - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < num_cols
            invariant
                0 <= c <= num_cols,
                row.len() == c,
                0 <= r < num_rows,
                1 <= num_cols <= 10_000,
                num_rows * num_cols <= 10_000,
                flat_values.len() == num_rows * num_cols,
                forall|i: int| 0 <= i < flat_values.len() ==> -100_000 <= #[trigger] flat_values[i] <= 100_000,
                forall|cc: int| 0 <= cc < c ==> -100_000 <= #[trigger] row[cc] <= 100_000,
            decreases num_cols - c,
        {
            proof {
                assert(r * num_cols + c < num_rows * num_cols) by (nonlinear_arith)
                    requires r < num_rows, c < num_cols, num_cols >= 1;
            }
            let idx = r * num_cols + c;
            let v = flat_values[idx];
            let val: i32 = if mutation_kind == 1 {
                0i32
            } else if mutation_kind == 2 {
                100_000i32
            } else if mutation_kind == 3 {
                -100_000i32
            } else if mutation_kind == 4 {
                let neg = -v;
                neg
            } else {
                v
            };
            assert(-100_000 <= val <= 100_000);
            row.push(val);
            c += 1;
        }
        mat.push(row);
        r += 1;
    }
    proof {
        // mat.len() == num_rows >= 1, so mat[0] is valid
        assert(mat.len() == num_rows);
        assert(mat[0int].len() == num_cols);
        assert(mat.len() * mat[0int].len() <= 10_000) by (nonlinear_arith)
            requires mat.len() == num_rows, mat[0int].len() == num_cols, num_rows * num_cols <= 10_000;
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
    let mut vals = Vec::with_capacity(count);
    for _ in 0..count {
        vals.push(rng.gen_range_i64(-100_000, 100_000) as i32);
    }
    vals
}

/// Pick (rows, cols) such that rows * cols <= 10_000 and both >= 1.
fn random_dims(rng: &mut Rng, max_total: usize) -> (usize, usize) {
    let rows = rng.gen_range_usize(1, max_total);
    let cols = rng.gen_range_usize(1, max_total / rows);
    (rows, cols)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(498);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n = 0usize;

    let mut emit = |mat: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, n: &mut usize| {
        if *n >= count { return; }
        let key = format!("{:?}", mat);
        if !seen.insert(key) { return; }
        let output = Solution::find_diagonal_order(mat.clone());
        writeln!(out, "{}", json!({"input": {"mat": mat}, "output": output})).unwrap();
        *n += 1;
    };

    // Example 1: [[1,2,3],[4,5,6],[7,8,9]]
    emit(
        vec![vec![1,2,3], vec![4,5,6], vec![7,8,9]],
        &mut seen, &mut out, &mut n,
    );
    // Example 2: [[1,2],[3,4]]
    emit(
        vec![vec![1,2], vec![3,4]],
        &mut seen, &mut out, &mut n,
    );
    // 1x1
    emit(vec![vec![42]], &mut seen, &mut out, &mut n);
    // Single row
    emit(vec![vec![1,2,3,4,5]], &mut seen, &mut out, &mut n);
    // Single column
    emit(vec![vec![1],vec![2],vec![3],vec![4]], &mut seen, &mut out, &mut n);
    // Boundary values
    emit(vec![vec![100_000, -100_000], vec![-100_000, 100_000]], &mut seen, &mut out, &mut n);
    // All zeros
    emit(vec![vec![0,0,0],vec![0,0,0]], &mut seen, &mut out, &mut n);

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    // Structured diverse sizes via generate_test_case + mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 1), (1, 2), (2, 1), (2, 2), (2, 3), (3, 2),
        (3, 3), (4, 4), (5, 5), (1, 10), (10, 1),
        (10, 10), (1, 100), (100, 1), (20, 20),
        (50, 50), (100, 100), (1, 10000), (10000, 1),
        (50, 200), (200, 50),
    ];

    for &(rows, cols) in &size_classes {
        if rows * cols > 10_000 { continue; }
        for &mk in &mutation_kinds {
            if n >= count { break; }
            let flat = random_flat_values(&mut rng, rows * cols);
            let mat = generate_test_case(rows, cols, flat, mk);
            emit(mat, &mut seen, &mut out, &mut n);
        }
    }

    // Random sizes with random mutations
    while n < count {
        let total = match n % 5 {
            0 => rng.gen_range_usize(1, 4),       // tiny
            1 => rng.gen_range_usize(1, 25),      // small
            2 => rng.gen_range_usize(10, 100),    // medium
            3 => rng.gen_range_usize(100, 1000),  // large
            _ => rng.gen_range_usize(1000, 10000),// max
        };
        let rows = rng.gen_range_usize(1, total);
        let cols = total / rows;
        if cols < 1 || rows * cols > 10_000 { continue; }
        let mk = rng.gen_range_usize(0, 4) as u8;
        let flat = random_flat_values(&mut rng, rows * cols);
        let mat = generate_test_case(rows, cols, flat, mk);
        emit(mat, &mut seen, &mut out, &mut n);
    }
}
