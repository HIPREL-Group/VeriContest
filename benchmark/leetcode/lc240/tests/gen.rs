use vstd::prelude::*;

verus! {

pub open spec fn cell_val(base: int, row_step: int, col_step: int, i: int, j: int) -> int {
    base + i * row_step + j * col_step
}

pub fn generate_test_case(
    m: usize,
    n: usize,
    base: i32,
    row_step: i32,
    col_step: i32,
    target: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= m <= 300,
        1 <= n <= 300,
        row_step >= 1,
        col_step >= 1,
        -1_000_000_000 <= base as int,
        base as int + (m - 1) as int * row_step as int + (n - 1) as int * col_step as int <= 1_000_000_000,
        -1_000_000_000 <= target <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 300,
        1 <= result.0[0].len() <= 300,
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == result.0[0].len(),
        forall |i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len()
            ==> -1_000_000_000 <= #[trigger] result.0[i][j] <= 1_000_000_000,
        forall |i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len() - 1 ==>
            #[trigger] result.0[i][j] < result.0[i][j + 1],
        forall |i: int, j: int| 0 <= j < result.0[0].len() && 0 <= i < result.0.len() - 1 ==>
            #[trigger] result.0[i][j] < result.0[i + 1][j],
        -1_000_000_000 <= result.1 <= 1_000_000_000,
{
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;

    while r < m
        invariant
            0 <= r <= m,
            1 <= m <= 300,
            1 <= n <= 300,
            row_step >= 1i32,
            col_step >= 1i32,
            -1_000_000_000 <= base as int,
            base as int + (m - 1) as int * row_step as int + (n - 1) as int * col_step as int <= 1_000_000_000,
            matrix.len() == r as int,
            forall |i: int| 0 <= i < r as int
                ==> (#[trigger] matrix[i]).len() == n as int,
            forall |i: int, j: int| 0 <= i < r as int && 0 <= j < n as int
                ==> (#[trigger] matrix[i][j]) as int == cell_val(base as int, row_step as int, col_step as int, i, j),
        decreases m - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;

        while c < n
            invariant
                0 <= c <= n,
                1 <= n <= 300,
                0 <= r < m,
                1 <= m <= 300,
                row_step >= 1i32,
                col_step >= 1i32,
                -1_000_000_000 <= base as int,
                base as int + (m - 1) as int * row_step as int + (n - 1) as int * col_step as int <= 1_000_000_000,
                row.len() == c as int,
                forall |j: int| 0 <= j < c as int
                    ==> (#[trigger] row[j]) as int == cell_val(base as int, row_step as int, col_step as int, r as int, j),
            decreases n - c,
        {
            proof {
                assert(r as int * (row_step as int) <= (m - 1) as int * (row_step as int)) by(nonlinear_arith)
                    requires r as int <= (m - 1) as int, row_step as int >= 1;
                assert(c as int * (col_step as int) <= (n - 1) as int * (col_step as int)) by(nonlinear_arith)
                    requires c as int <= (n - 1) as int, col_step as int >= 1;
                assert(r as int * (row_step as int) >= 0) by(nonlinear_arith)
                    requires r as int >= 0, row_step as int >= 1;
                assert(c as int * (col_step as int) >= 0) by(nonlinear_arith)
                    requires c as int >= 0, col_step as int >= 1;
            }
            let val_i64: i64 = (base as i64) + (r as i64) * (row_step as i64) + (c as i64) * (col_step as i64);
            let val: i32 = val_i64 as i32;
            assert(val as int == cell_val(base as int, row_step as int, col_step as int, r as int, c as int));
            row.push(val);
            c += 1;
        }

        assert(row.len() == n as int);

        let ghost prev_matrix_len = matrix.len();
        matrix.push(row);

        proof {
            assert forall |i: int| 0 <= i < r as int + 1
                implies (#[trigger] matrix[i]).len() == n as int
            by {}

            assert forall |i: int, j: int|
                0 <= i < r as int + 1 && 0 <= j < n as int
                implies (#[trigger] matrix[i][j]) as int == cell_val(base as int, row_step as int, col_step as int, i, j)
            by {}
        }

        r += 1;
    }

    // Derive ensures from cell_val formula
    proof {
        // Row ordering: cell_val(i, j+1) - cell_val(i, j) = col_step >= 1
        assert forall |i: int, j: int|
            0 <= i < matrix.len() && 0 <= j < n as int - 1
            implies (#[trigger] matrix[i][j]) < matrix[i][j + 1]
        by {
            assert(matrix[i][j] as int == cell_val(base as int, row_step as int, col_step as int, i, j));
            assert(matrix[i][j + 1] as int == cell_val(base as int, row_step as int, col_step as int, i, j + 1));
            assert((j + 1) * (col_step as int) == j * (col_step as int) + col_step as int) by(nonlinear_arith);
        }

        // Column ordering: cell_val(i+1, j) - cell_val(i, j) = row_step >= 1
        assert forall |i: int, j: int|
            0 <= j < n as int && 0 <= i < m as int - 1
            implies (#[trigger] matrix[i][j]) < matrix[i + 1][j]
        by {
            assert(matrix[i][j] as int == cell_val(base as int, row_step as int, col_step as int, i, j));
            assert(matrix[i + 1][j] as int == cell_val(base as int, row_step as int, col_step as int, i + 1, j));
            assert((i + 1) * (row_step as int) == i * (row_step as int) + row_step as int) by(nonlinear_arith);
        }

        // Value bounds
        assert forall |i: int, j: int|
            0 <= i < m as int && 0 <= j < n as int
            implies -1_000_000_000 <= (#[trigger] matrix[i][j]) as int <= 1_000_000_000
        by {
            assert(matrix[i][j] as int == cell_val(base as int, row_step as int, col_step as int, i, j));
            assert(i * (row_step as int) <= (m - 1) as int * (row_step as int)) by(nonlinear_arith)
                requires 0 <= i, i <= (m - 1) as int, row_step as int >= 1;
            assert(j * (col_step as int) <= (n - 1) as int * (col_step as int)) by(nonlinear_arith)
                requires 0 <= j, j <= (n - 1) as int, col_step as int >= 1;
            assert(i * (row_step as int) >= 0) by(nonlinear_arith)
                requires i >= 0, row_step as int >= 1;
            assert(j * (col_step as int) >= 0) by(nonlinear_arith)
                requires j >= 0, col_step as int >= 1;
        }
    }

    // Target mutations
    let final_target: i32 = if mutation_kind == 0 {
        target
    } else if mutation_kind == 1 {
        base
    } else if mutation_kind == 2 {
        let v: i64 = (base as i64) + ((m - 1) as i64) * (row_step as i64) + ((n - 1) as i64) * (col_step as i64);
        v as i32
    } else if mutation_kind == 3 {
        let mr = m / 2;
        let mc = n / 2;
        proof {
            assert((mr as int) * (row_step as int) <= (m - 1) as int * (row_step as int)) by(nonlinear_arith)
                requires mr as int <= (m - 1) as int, row_step as int >= 1;
            assert((mc as int) * (col_step as int) <= (n - 1) as int * (col_step as int)) by(nonlinear_arith)
                requires mc as int <= (n - 1) as int, col_step as int >= 1;
            assert((mr as int) * (row_step as int) >= 0) by(nonlinear_arith)
                requires mr as int >= 0, row_step as int >= 1;
            assert((mc as int) * (col_step as int) >= 0) by(nonlinear_arith)
                requires mc as int >= 0, col_step as int >= 1;
        }
        let v: i64 = (base as i64) + (mr as i64) * (row_step as i64) + (mc as i64) * (col_step as i64);
        v as i32
    } else if mutation_kind == 4 && base > -1_000_000_000 {
        (base - 1)
    } else if mutation_kind == 5 {
        let max_v: i64 = (base as i64) + ((m - 1) as i64) * (row_step as i64) + ((n - 1) as i64) * (col_step as i64);
        if max_v < 1_000_000_000 {
            (max_v + 1) as i32
        } else {
            target
        }
    } else {
        target
    };

    (matrix, final_target)
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

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(240);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |matrix: Vec<Vec<i32>>, target: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= count_target { return; }
        let key = format!("{:?},{}", matrix, target);
        if !seen.insert(key) { return; }
        let output = Solution::search_matrix(matrix.clone(), target);
        writeln!(out, "{}", json!({
            "input": {"matrix": matrix, "target": target},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let ex_matrix = vec![
        vec![1,4,7,11,15],
        vec![2,5,8,12,19],
        vec![3,6,9,16,22],
        vec![10,13,14,17,24],
        vec![18,21,23,26,30],
    ];
    for &t in &[5, 20, 1, 30, 0, -1, 31] {
        emit(ex_matrix.clone(), t, &mut seen, &mut out, &mut count);
    }

    // Size classes for (m, n)
    let size_configs: Vec<(usize, usize)> = vec![
        (1, 1), (1, 2), (2, 1), (1, 5), (5, 1),
        (2, 2), (3, 3), (5, 5), (10, 10),
        (1, 300), (300, 1), (20, 20), (50, 50),
        (100, 100), (150, 150), (300, 300),
        (1, 100), (100, 1), (3, 100), (100, 3),
    ];

    // Generate structured test cases with the formula approach
    for &(m, n) in &size_configs {
        if count >= count_target { break; }

        let base_vals: Vec<i32> = vec![0, -1_000_000_000, -100, 100];
        for &base in &base_vals {
            if count >= count_target { break; }

            let budget = 1_000_000_000i64 - base as i64;
            if budget <= 0 { continue; }

            let max_row_step = if m > 1 { budget / (2 * (m as i64 - 1)) } else { budget / 2 };
            let max_col_step = if n > 1 { budget / (2 * (n as i64 - 1)) } else { budget / 2 };
            if max_row_step < 1 || max_col_step < 1 { continue; }

            let row_step = std::cmp::max(1, std::cmp::min(max_row_step, rng.gen_range_i64(1, max_row_step))) as i32;
            let col_step = std::cmp::max(1, std::cmp::min(max_col_step, rng.gen_range_i64(1, max_col_step))) as i32;

            let max_val = base as i64 + (m as i64 - 1) * row_step as i64 + (n as i64 - 1) * col_step as i64;
            if max_val > 1_000_000_000 { continue; }

            for mk in 0..=5u8 {
                if count >= count_target { break; }
                let target_val: i32 = match mk {
                    0 => rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32,
                    _ => 0,
                };
                let (mat, tgt) = generate_test_case(m, n, base, row_step, col_step, target_val, mk);
                emit(mat, tgt, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Fill remaining with random test cases
    while count < count_target {
        let m = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 150),
            _ => rng.gen_range_usize(150, 300),
        };
        let n = match count % 7 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 150),
            4 => rng.gen_range_usize(150, 300),
            5 => 1,
            _ => 300,
        };

        let base: i32 = if count % 5 == 0 {
            *[-1_000_000_000i32, 0, 1_000_000_000].iter().nth(count % 3).unwrap()
        } else {
            rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32
        };

        let budget = 1_000_000_000i64 - base as i64;
        if budget <= 0 { continue; }

        let denom_r = std::cmp::max(1, m as i64 - 1);
        let denom_c = std::cmp::max(1, n as i64 - 1);
        let max_rs = std::cmp::max(1, budget / (2 * denom_r));
        let max_cs = std::cmp::max(1, budget / (2 * denom_c));

        let row_step = rng.gen_range_i64(1, std::cmp::min(max_rs, i32::MAX as i64)) as i32;
        let col_step = rng.gen_range_i64(1, std::cmp::min(max_cs, i32::MAX as i64)) as i32;

        let max_val = base as i64 + (m as i64 - 1) * row_step as i64 + (n as i64 - 1) * col_step as i64;
        if max_val > 1_000_000_000 || (base as i64) < -1_000_000_000 { continue; }

        let target_val = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
        let mk = (count % 6) as u8;

        let (mat, tgt) = generate_test_case(m, n, base, row_step, col_step, target_val, mk);
        emit(mat, tgt, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
