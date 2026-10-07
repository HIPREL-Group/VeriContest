use vstd::prelude::*;

verus! {

spec fn cell_value(r: int, c: int, cols: int, total: int, descending: bool) -> int {
    if descending { total - r * cols - c }
    else { r * cols + c + 1 }
}

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    mutation_kind: u8,
) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= rows <= 500,
        1 <= cols <= 500,
        rows * cols <= 100_000,
    ensures
        1 <= mat.len() <= 500,
        forall |i: int| 0 <= i < mat.len() ==> 1 <= #[trigger] mat[i].len() <= 500,
        forall |i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
        forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==> 1 <= #[trigger] mat[i][j] <= 100_000,
        forall |i: int, j: int|
            0 <= i && i + 1 < mat.len() && 0 <= j < mat[0].len() ==> #[trigger] mat[i][j] != mat[i + 1][j],
        forall |i: int, j: int|
            0 <= i < mat.len() && 0 <= j && j + 1 < mat[0].len() ==> #[trigger] mat[i][j] != mat[i][j + 1],
{
    let descending: bool = mutation_kind == 1;
    let total: usize = rows * cols;
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            0 <= i <= rows,
            1 <= rows <= 500,
            1 <= cols <= 500,
            total == rows * cols,
            total <= 100_000,
            descending == (mutation_kind == 1u8),
            mat.len() == i as int,
            forall |r: int| 0 <= r < i as int
                ==> (#[trigger] mat[r]).len() == cols as int,
            forall |r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int
                ==> (#[trigger] mat[r][c]) as int
                    == cell_value(r, c, cols as int, total as int, descending),
        decreases rows - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                0 <= j <= cols,
                0 <= i < rows,
                1 <= rows <= 500,
                1 <= cols <= 500,
                total == rows * cols,
                total <= 100_000,
                descending == (mutation_kind == 1u8),
                row.len() == j as int,
                forall |c: int| 0 <= c < j as int
                    ==> (#[trigger] row[c]) as int
                        == cell_value(i as int, c, cols as int, total as int, descending),
            decreases cols - j,
        {
            proof {
                assert(i * cols + j < total) by(nonlinear_arith)
                    requires i < rows, j < cols, total == rows * cols, cols >= 1, rows >= 1,
                {};
                assert(i * cols + j + 1 <= total) by(nonlinear_arith)
                    requires i < rows, j < cols, total == rows * cols, cols >= 1, rows >= 1,
                {};
                assert(total - i * cols - j >= 1) by(nonlinear_arith)
                    requires i < rows, j < cols, total == rows * cols, cols >= 1, rows >= 1,
                {};
                assert(total - i * cols - j <= total) by(nonlinear_arith)
                    requires 0 <= i, 0 <= j,
                {};
            }
            let val: i32;
            if descending {
                val = (total - i * cols - j) as i32;
            } else {
                val = (i * cols + j + 1) as i32;
            }
            row.push(val);
            j += 1;
        }
        mat.push(row);
        i += 1;
    }

    proof {
        assert(1 <= mat.len() <= 500);

        assert forall |r: int| 0 <= r < mat.len()
            implies 1 <= #[trigger] mat[r].len() <= 500
        by {};

        assert forall |r: int| 0 <= r < mat.len()
            implies #[trigger] mat[r].len() == mat[0].len()
        by {};

        assert forall |r: int, c: int|
            0 <= r < mat.len() && 0 <= c < mat[0].len()
            implies 1 <= #[trigger] mat[r][c] <= 100_000
        by {
            assert(mat[r][c] as int == cell_value(r, c, cols as int, total as int, descending));
            if descending {
                assert(total as int - r * (cols as int) - c >= 1) by(nonlinear_arith)
                    requires 0 <= r, r < rows, 0 <= c, c < cols,
                    total == rows * cols, cols >= 1, rows >= 1,
                {};
            } else {
                assert(r * (cols as int) + c + 1 <= total as int) by(nonlinear_arith)
                    requires 0 <= r, r < rows, 0 <= c, c < cols,
                    total == rows * cols, cols >= 1, rows >= 1,
                {};
            }
        };

        assert forall |r: int, c: int|
            0 <= r && r + 1 < mat.len() && 0 <= c < mat[0].len()
            implies #[trigger] mat[r][c] != mat[r + 1][c]
        by {
            assert(mat[r][c] as int == cell_value(r, c, cols as int, total as int, descending));
            assert(mat[r + 1][c] as int == cell_value(r + 1, c, cols as int, total as int, descending));
            if descending {
                assert(mat[r][c] as int - mat[r + 1][c] as int == cols as int) by(nonlinear_arith)
                    requires
                        mat[r][c] as int == total as int - r * (cols as int) - c,
                        mat[r + 1][c] as int == total as int - (r + 1) * (cols as int) - c,
                {};
            } else {
                assert(mat[r + 1][c] as int - mat[r][c] as int == cols as int) by(nonlinear_arith)
                    requires
                        mat[r][c] as int == r * (cols as int) + c + 1,
                        mat[r + 1][c] as int == (r + 1) * (cols as int) + c + 1,
                {};
            }
        };

        assert forall |r: int, c: int|
            0 <= r < mat.len() && 0 <= c && c + 1 < mat[0].len()
            implies #[trigger] mat[r][c] != mat[r][c + 1]
        by {
            assert(mat[r][c] as int == cell_value(r, c, cols as int, total as int, descending));
            assert(mat[r][c + 1] as int == cell_value(r, c + 1, cols as int, total as int, descending));
            if descending {
                assert(cell_value(r, c, cols as int, total as int, descending)
                     - cell_value(r, c + 1, cols as int, total as int, descending) == 1);
            } else {
                assert(cell_value(r, c + 1, cols as int, total as int, descending)
                     - cell_value(r, c, cols as int, total as int, descending) == 1);
            }
        };
    }

    mat
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
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
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut total_count = 0usize;

    let mut emit = |mat: Vec<Vec<i32>>, out: &mut std::io::BufWriter<std::fs::File>, tc: &mut usize| {
        if *tc >= count { return; }
        let output = Solution::find_peak_grid(mat.clone());
        writeln!(out, "{}", json!({"input": {"mat": mat}, "output": output})).unwrap();
        *tc += 1;
    };

    // Example inputs from description.md
    emit(vec![vec![1, 4], vec![3, 2]], &mut out, &mut total_count);
    emit(vec![vec![10, 20, 15], vec![21, 30, 14], vec![7, 16, 32]], &mut out, &mut total_count);

    // Fixed sizes x mutation kinds (ascending=0, descending=1)
    let sizes: Vec<(usize, usize)> = vec![
        (1, 1), (1, 2), (2, 1), (2, 2),
        (1, 500), (500, 1),
        (5, 5), (10, 10), (20, 20),
        (100, 100), (200, 500), (500, 200), (316, 316),
        (3, 7), (50, 50),
    ];

    for &(r, c) in &sizes {
        for mk in 0..2u8 {
            if total_count >= count { break; }
            if r * c > 100_000 { continue; }
            let mat = generate_test_case(r, c, mk);
            emit(mat, &mut out, &mut total_count);
        }
    }

    // Random sizes with size classes
    while total_count < count {
        let rows = match total_count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 500),
        };
        let max_cols = std::cmp::min(500, 100_000 / rows);
        if max_cols < 1 { continue; }
        let cols = rng.gen_range_usize(1, max_cols);
        let mk = rng.gen_range_usize(0, 1) as u8;
        let mat = generate_test_case(rows, cols, mk);
        emit(mat, &mut out, &mut total_count);
    }
}
