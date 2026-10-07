use vstd::prelude::*;

verus! {

pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

proof fn lemma_sum_deltas_mono(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

proof fn lemma_sum_deltas_strict(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a < b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) + (b - a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if b - a == 1 {
    } else {
        lemma_sum_deltas_strict(deltas, a, b - 1);
    }
}

pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    rows: usize,
    cols: usize,
    target: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= rows <= 100,
        1 <= cols <= 100,
        (rows as int) * (cols as int) <= 10_000,
        deltas.len() as int == (rows as int) * (cols as int) - 1,
        -10_000 <= base <= 10_000,
        -10_000 <= target <= 10_000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 10_000,
    ensures
        1 <= result.0.len() <= 100,
        1 <= result.0[0].len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == result.0[0].len(),
        forall |i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len()
            ==> -10_000 <= #[trigger] result.0[i][j] <= 10_000,
        forall |i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len() - 1 ==>
            #[trigger] result.0[i][j] <= result.0[i][j + 1],
        forall |i: int| 1 <= i < result.0.len() ==>
            #[trigger] result.0[i][0] > result.0[i - 1][result.0[0].len() - 1],
        -10_000 <= result.1 <= 10_000,
{
    // Build flat strictly-increasing array: flat[k] = base + sum(deltas[0..k])
    let mut flat: Vec<i32> = Vec::new();
    flat.push(base);

    let mut k: usize = 0;
    while k < deltas.len()
        invariant
            0 <= k <= deltas.len(),
            flat.len() == (k + 1) as int,
            deltas.len() as int == (rows as int) * (cols as int) - 1,
            (rows as int) * (cols as int) <= 10_000,
            1 <= rows <= 100,
            1 <= cols <= 100,
            -10_000 <= base <= 10_000,
            forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 10_000,
            forall|i: int| #![auto] 0 <= i <= k as int ==>
                flat[i] == (base as int + sum_deltas(deltas@, i)) as i32,
            forall|i: int| #![auto] 0 <= i <= k as int ==>
                flat[i] as int == base as int + sum_deltas(deltas@, i),
            forall|i: int| 0 <= i < flat.len() ==> -10_000 <= #[trigger] flat[i] <= 10_000,
            forall|i: int, j: int| 0 <= i < j < flat.len() ==> flat[i] < flat[j],
        decreases deltas.len() - k,
    {
        let ghost old_len = flat.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (k + 1) as int, deltas.len() as int);
        }

        let next = flat[k] + deltas[k];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (k + 1) as int));
            assert(-10_000 <= next <= 10_000) by {
                lemma_sum_deltas_mono(deltas@, 0, (k + 1) as int);
            };

            assert forall|i: int| 0 <= i < flat.len() implies flat[i] < next by {
                assert(flat[i] as int == base as int + sum_deltas(deltas@, i));
                lemma_sum_deltas_strict(deltas@, i, (k + 1) as int);
            };
        }

        flat.push(next);
        k = k + 1;

        proof {
            assert forall|i: int, j: int| 0 <= i < j < flat.len() implies flat[i] < flat[j] by {
                if j < old_len as int {
                } else {
                    assert(j == old_len as int);
                    assert(flat[j] == next);
                }
            };
        }
    }

    assert(flat.len() as int == (rows as int) * (cols as int));

    // Reshape flat into matrix using a running flat index.
    // Track prev_row_last to prove cross-row ordering without nonlinear arithmetic.
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    let mut fi: usize = 0;
    let ghost mut prev_row_last: int = 0; // dummy, unused when r == 0
    while r < rows
        invariant
            0 <= r <= rows,
            1 <= rows <= 100,
            1 <= cols <= 100,
            0 <= fi <= flat.len(),
            matrix.len() == r as int,
            flat.len() as int == (rows as int) * (cols as int),
            (rows as int) * (cols as int) <= 10_000,
            forall|i: int| 0 <= i < flat.len() ==> -10_000 <= #[trigger] flat[i] <= 10_000,
            forall|i: int, j: int| 0 <= i < j < flat.len() ==> flat[i] < flat[j],
            // All rows have cols elements
            forall|i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == cols as int,
            // Values in range
            forall|i: int, j: int| 0 <= i < matrix.len() && 0 <= j < cols as int ==>
                -10_000 <= #[trigger] matrix[i][j] <= 10_000,
            // Each row strictly increasing
            forall|i: int, j1: int, j2: int|
                0 <= i < matrix.len() && 0 <= j1 < j2 < cols as int ==>
                matrix[i][j1] < matrix[i][j2],
            // Cross-row ordering
            forall|i: int| 1 <= i < matrix.len() ==>
                matrix[i - 1][cols as int - 1] < #[trigger] matrix[i][0],
            // The first element of the next row we build will be flat[fi],
            // and prev_row_last tracks the last element of the previous row
            r > 0 ==> (
                prev_row_last == matrix[(r - 1) as int][cols as int - 1] as int &&
                fi > 0 &&
                flat[(fi - 1) as int] as int == prev_row_last
            ),
            // fi still has rows * cols - fi elements left, enough for remaining rows
            fi <= flat.len(),
            fi + (rows - r) * cols == flat.len(),
        decreases rows - r,
    {
        let row_start = fi;
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;

        proof {
            // Prove row_start + cols <= flat.len() from fi + (rows - r) * cols == flat.len()
            // Since r < rows, (rows - r) >= 1, so fi + cols <= fi + (rows - r) * cols
            assert(row_start + cols <= flat.len()) by(nonlinear_arith)
                requires
                    fi == row_start,
                    fi + (rows - r) * cols == flat.len(),
                    r < rows,
                    cols >= 1;
        }

        while c < cols
            invariant
                0 <= c <= cols,
                1 <= cols <= 100,
                row.len() == c as int,
                fi == row_start + c,
                0 <= row_start,
                row_start + cols <= flat.len(),
                forall|i: int| 0 <= i < flat.len() ==> -10_000 <= #[trigger] flat[i] <= 10_000,
                forall|i: int, j: int| 0 <= i < j < flat.len() ==> flat[i] < flat[j],
                forall|j: int| 0 <= j < c as int ==>
                    (#[trigger] row[j]) == flat[row_start as int + j],
            decreases cols - c,
        {
            row.push(flat[fi]);
            fi = fi + 1;
            c = c + 1;
        }

        assert(row.len() == cols as int);
        assert(fi == row_start + cols);

        // Prove row properties
        proof {
            assert forall|j: int| 0 <= j < cols as int
                implies -10_000 <= (#[trigger] row[j]) <= 10_000 by {
                assert(row[j] == flat[row_start as int + j]);
            };

            assert forall|j1: int, j2: int| 0 <= j1 < j2 < cols as int
                implies row[j1] < row[j2] by {
                assert(row[j1] == flat[row_start as int + j1]);
                assert(row[j2] == flat[row_start as int + j2]);
                assert(row_start as int + j1 < row_start as int + j2);
            };
        }

        // Record the first and last of the new row
        let ghost new_row_first = row[0] as int;
        let ghost new_row_last = row[(cols - 1) as int] as int;

        proof {
            // The first element of the new row = flat[row_start]
            assert(row[0] == flat[row_start as int]);
            // The last element of the new row = flat[row_start + cols - 1]
            assert(row[cols as int - 1] == flat[row_start as int + cols as int - 1]);

            // Cross-row: if r > 0, then prev row's last = flat[row_start - 1]
            // and current row's first = flat[row_start]
            // Since row_start - 1 < row_start, flat[row_start-1] < flat[row_start]
            if r > 0 {
                let ghost rs = row_start as int;
                let ghost rs_m1 = (row_start - 1) as int;
                assert(prev_row_last == flat[rs_m1] as int);
                assert(rs_m1 < rs);
                assert(flat[rs_m1] < flat[rs]);
            }
        }

        matrix.push(row);

        proof {
            assert forall|i: int| 0 <= i < matrix.len()
                implies #[trigger] matrix[i].len() == cols as int by {
                if i < r as int {} else {}
            };
            assert forall|i: int, j: int| 0 <= i < matrix.len() && 0 <= j < cols as int
                implies -10_000 <= #[trigger] matrix[i][j] <= 10_000 by {
                if i < r as int {} else {}
            };
            assert forall|i: int, j1: int, j2: int|
                0 <= i < matrix.len() && 0 <= j1 < j2 < cols as int
                implies matrix[i][j1] < matrix[i][j2] by {
                if i < r as int {} else {}
            };

            // Cross-row for the newly added row
            if r > 0 {
                assert forall|i: int| 1 <= i < matrix.len()
                    implies matrix[i - 1][cols as int - 1] < #[trigger] matrix[i][0] by {
                    if i < r as int {
                        // Old rows — from invariant
                    } else {
                        // i == r: the new row
                        assert(i == r as int);
                        // matrix[r][0] is the new row's first
                        // matrix[r-1][cols-1] is prev row's last
                        assert(matrix[r as int][0] == flat[row_start as int]);
                        assert(prev_row_last == flat[(row_start - 1) as int] as int);
                        assert(matrix[(r - 1) as int][cols as int - 1] as int == prev_row_last);
                        assert(flat[(row_start - 1) as int] < flat[row_start as int]);
                    }
                };
            }
        }

        r = r + 1;

        proof {
            prev_row_last = new_row_last;
            // Prove fi + (rows - r) * cols == flat.len()
            // old: (fi - cols) + (rows - (r - 1)) * cols == flat.len()
            // new: fi + (rows - r) * cols
            //    = (fi - cols) + cols + (rows - r) * cols
            //    = (fi - cols) + (1 + rows - r) * cols
            //    = (fi - cols) + (rows - (r-1)) * cols
            //    = flat.len()
            assert(fi + (rows - r) * cols == flat.len()) by(nonlinear_arith)
                requires
                    fi == row_start + cols,
                    row_start + (rows - (r - 1)) * cols == flat.len(),
                    r >= 1,
                    cols >= 1;
        }
    }

    assert(matrix.len() == rows as int);

    proof {
        assert(1 <= matrix.len() <= 100);
        assert(matrix[0].len() == cols as int);
        assert(1 <= matrix[0].len() <= 100);

        assert forall|i: int| 0 <= i < matrix.len()
            implies #[trigger] matrix[i].len() == matrix[0].len() by {};

        assert forall|i: int, j: int|
            0 <= i < matrix.len() && 0 <= j < matrix[i].len() - 1
            implies #[trigger] matrix[i][j] <= matrix[i][j + 1] by {
            assert(matrix[i][j] < matrix[i][j + 1]);
        };

        assert forall|i: int| 1 <= i < matrix.len()
            implies #[trigger] matrix[i][0] > matrix[i - 1][matrix[0].len() - 1] by {
            assert(matrix[0].len() == cols as int);
            assert(matrix[i - 1][cols as int - 1] < matrix[i][0]);
        };
    }

    // Compute mutated target
    let mutated_target: i32 =
        if mutation_kind == 1 {
            matrix[0][0]
        } else if mutation_kind == 2 {
            let lr = matrix.len() - 1;
            let lc = matrix[lr].len() - 1;
            matrix[lr][lc]
        } else if mutation_kind == 3 && rows >= 2 && cols >= 2 {
            let mid_r = rows / 2;
            let mid_c = cols / 2;
            assert(mid_r < rows);
            assert(mid_c < cols) by {
                assert(matrix[mid_r as int].len() == cols as int);
            };
            matrix[mid_r][mid_c]
        } else if mutation_kind == 4 && matrix[0][0] > -10_000 {
            (matrix[0][0] - 1) as i32
        } else if mutation_kind == 5 {
            let lr = matrix.len() - 1;
            let lc = matrix[lr].len() - 1;
            if matrix[lr][lc] < 10_000 {
                (matrix[lr][lc] + 1) as i32
            } else {
                target
            }
        } else if mutation_kind == 6 && cols >= 2 {
            if matrix[0][1] - matrix[0][0] > 1 {
                (matrix[0][0] + 1) as i32
            } else {
                target
            }
        } else {
            target
        };

    (matrix, mutated_target)
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

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n {
        deltas.push(rng.gen_range_i64(1, max_d as i64) as i32);
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(74);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $rows:expr, $cols:expr, $target:expr, $mk:expr) => {
            if count < goal {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let rows_val: usize = $rows;
                let cols_val: usize = $cols;
                let target_val: i32 = $target;
                let mk_val: u8 = $mk;
                let (matrix_out, target_out) = generate_test_case(
                    &deltas_val, base_val, rows_val, cols_val, target_val, mk_val,
                );
                let result = Solution::search_matrix(matrix_out.clone(), target_out);
                let line = json!({
                    "input": {"matrix": matrix_out, "target": target_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    // Example 1: [[1,3,5,7],[10,11,16,20],[23,30,34,60]], target = 3
    emit!(vec![2,2,2,3,1,5,4,3,7,4,26], 1, 3, 4, 3, 0);
    // Example 2: same matrix, target = 13
    emit!(vec![2,2,2,3,1,5,4,3,7,4,26], 1, 3, 4, 13, 0);

    // ---- Single element matrix, all mutations ----
    for mk in 0u8..=6 {
        emit!(vec![], 0, 1, 1, 5, mk);
        emit!(vec![], -10_000, 1, 1, 0, mk);
        emit!(vec![], 10_000, 1, 1, 0, mk);
    }

    // ---- Single row, multiple columns ----
    for mk in 0u8..=6 {
        emit!(vec![1, 1, 1], 0, 1, 4, 2, mk);
    }

    // ---- Single column, multiple rows ----
    for mk in 0u8..=6 {
        emit!(vec![1, 1, 1], 0, 4, 1, 2, mk);
    }

    // ---- 2x2 matrix, all mutations ----
    for mk in 0u8..=6 {
        emit!(vec![1, 1, 1], -5, 2, 2, 0, mk);
        emit!(vec![10, 10, 10], -100, 2, 2, 0, mk);
    }

    // ---- Near boundary values ----
    emit!(vec![1; 3], 9_997, 2, 2, 9_999, 0);
    emit!(vec![1; 3], -10_000, 2, 2, -9_998, 0);

    // ---- Random tiny matrices (2-9 total), all mutations ----
    for _ in 0..4 {
        let rows = rng.gen_range_usize(1, 3);
        let cols = rng.gen_range_usize(1, 3);
        let n = rows * cols;
        if n == 0 { continue; }
        let num_deltas = n - 1;
        let max_d = std::cmp::max(1, (20_000i64 / std::cmp::max(num_deltas, 1) as i64) as i32);
        let deltas = random_deltas(&mut rng, num_deltas, std::cmp::min(max_d, 100));
        let total_sum: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10_000i64, 10_000 - total_sum);
        let base = if hi < -10_000 { -10_000i32 } else { rng.gen_range_i64(-10_000, hi) as i32 };
        let t = rng.gen_range_i64(-10_000, 10_000) as i32;
        for mk in 0u8..=6 {
            emit!(deltas.clone(), base, rows, cols, t, mk);
        }
    }

    // ---- Random small matrices (rows*cols ~ 10-50) ----
    for _ in 0..6 {
        let rows = rng.gen_range_usize(2, 7);
        let cols = rng.gen_range_usize(2, 7);
        let n = rows * cols;
        let num_deltas = n - 1;
        let max_d = std::cmp::max(1, (20_000i64 / num_deltas as i64) as i32);
        let deltas = random_deltas(&mut rng, num_deltas, std::cmp::min(max_d, 50));
        let total_sum: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10_000i64, 10_000 - total_sum);
        let base = if hi < -10_000 { -10_000i32 } else { rng.gen_range_i64(-10_000, hi) as i32 };
        let t = rng.gen_range_i64(-10_000, 10_000) as i32;
        let mk = (rng.gen_range_usize(0, 6) as u8) % 7;
        emit!(deltas.clone(), base, rows, cols, t, mk);
        emit!(deltas.clone(), base, rows, cols, t, 0);
    }

    // ---- Random medium matrices (rows*cols ~ 100-500) ----
    for _ in 0..6 {
        let rows = rng.gen_range_usize(5, 20);
        let cols = rng.gen_range_usize(5, 25);
        let n = rows * cols;
        if n > 10_000 { continue; }
        let num_deltas = n - 1;
        let max_d = std::cmp::max(1, (20_000i64 / num_deltas as i64) as i32);
        let deltas = random_deltas(&mut rng, num_deltas, std::cmp::min(max_d, 20));
        let total_sum: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10_000i64, 10_000 - total_sum);
        let base = if hi < -10_000 { -10_000i32 } else { rng.gen_range_i64(-10_000, hi) as i32 };
        let t = rng.gen_range_i64(-10_000, 10_000) as i32;
        let mk = (rng.gen_range_usize(0, 6) as u8) % 7;
        emit!(deltas.clone(), base, rows, cols, t, mk);
    }

    // ---- Large matrices (rows*cols ~ 1000-5000) ----
    for _ in 0..4 {
        let rows = rng.gen_range_usize(10, 50);
        let cols = rng.gen_range_usize(20, 100);
        let n = rows * cols;
        if n > 10_000 { continue; }
        let num_deltas = n - 1;
        let max_d = std::cmp::max(1, (20_000i64 / num_deltas as i64) as i32);
        let deltas = random_deltas(&mut rng, num_deltas, std::cmp::min(max_d, 5));
        let total_sum: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10_000i64, 10_000 - total_sum);
        let base = if hi < -10_000 { -10_000i32 } else { rng.gen_range_i64(-10_000, hi) as i32 };
        let t = rng.gen_range_i64(-10_000, 10_000) as i32;
        for mk in [0u8, 1, 2, 3] {
            emit!(deltas.clone(), base, rows, cols, t, mk);
        }
    }

    // ---- Maximum size: 100x100, delta=1 ----
    {
        let rows = 100;
        let cols = 100;
        let num_deltas = rows * cols - 1;
        let deltas = vec![1i32; num_deltas];
        let base = -5_000i32;
        for mk in 0u8..=5 {
            emit!(deltas.clone(), base, rows, cols, 0, mk);
        }
    }

    // ---- Fill remaining with random sizes and random mutations ----
    while count < goal {
        let rows = rng.gen_range_usize(1, 30);
        let cols = rng.gen_range_usize(1, 30);
        let n = rows * cols;
        if n == 0 || n > 10_000 { continue; }
        let num_deltas = n - 1;
        let max_d = std::cmp::max(1, (20_000i64 / std::cmp::max(num_deltas, 1) as i64) as i32);
        let deltas = random_deltas(&mut rng, num_deltas, std::cmp::min(max_d, 50));
        let total_sum: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10_000i64, 10_000 - total_sum);
        let base = if hi < -10_000 { -10_000i32 } else { rng.gen_range_i64(-10_000, hi) as i32 };
        let target = rng.gen_range_i64(-10_000, 10_000) as i32;
        let mk = (rng.gen_range_usize(0, 6) as u8) % 7;
        emit!(deltas, base, rows, cols, target, mk);
    }
}
