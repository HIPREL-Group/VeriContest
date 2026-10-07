use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    values: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= rows <= 1_000,
        1 <= cols <= 1_000,
        rows * cols <= 100_000,
        values.len() == rows * cols,
        forall|i: int| 0 <= i < values.len() ==> -1_000_000_000 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 1_000,
        1 <= result[0].len() <= 1_000,
        forall |r: int| 0 <= r < result.len() ==> #[trigger] result[r].len() == result[0].len(),
        result.len() * result[0].len() <= 100_000,
        forall |r: int, c: int| 0 <= r < result.len() && 0 <= c < result[r].len() ==> -1_000_000_000 <= #[trigger] result[r][c] <= 1_000_000_000,
{
    // Apply mutation to flat values before reshaping
    let mut vals = values;

    if mutation_kind == 1 {
        // set all to zero
        let mut k: usize = 0;
        while k < vals.len()
            invariant
                vals.len() == rows * cols,
                0 <= k <= vals.len(),
                forall|idx: int| 0 <= idx < k ==> vals[idx] == 0i32,
                forall|idx: int| k <= idx < vals.len() ==> -1_000_000_000 <= #[trigger] vals[idx] <= 1_000_000_000,
            decreases vals.len() - k,
        {
            vals.set(k, 0);
            k += 1;
        }
    } else if mutation_kind == 2 {
        // set all to max boundary
        let mut k: usize = 0;
        while k < vals.len()
            invariant
                vals.len() == rows * cols,
                0 <= k <= vals.len(),
                forall|idx: int| 0 <= idx < k ==> vals[idx] == 1_000_000_000i32,
                forall|idx: int| k <= idx < vals.len() ==> -1_000_000_000 <= #[trigger] vals[idx] <= 1_000_000_000,
            decreases vals.len() - k,
        {
            vals.set(k, 1_000_000_000);
            k += 1;
        }
    } else if mutation_kind == 3 {
        // set all to min boundary
        let mut k: usize = 0;
        while k < vals.len()
            invariant
                vals.len() == rows * cols,
                0 <= k <= vals.len(),
                forall|idx: int| 0 <= idx < k ==> vals[idx] == -1_000_000_000i32,
                forall|idx: int| k <= idx < vals.len() ==> -1_000_000_000 <= #[trigger] vals[idx] <= 1_000_000_000,
            decreases vals.len() - k,
        {
            vals.set(k, -1_000_000_000);
            k += 1;
        }
    } else if mutation_kind == 4 {
        // absolute value of each element
        let mut k: usize = 0;
        while k < vals.len()
            invariant
                vals.len() == rows * cols,
                0 <= k <= vals.len(),
                forall|idx: int| 0 <= idx < k ==> 0 <= #[trigger] vals[idx] <= 1_000_000_000,
                forall|idx: int| k <= idx < vals.len() ==> -1_000_000_000 <= #[trigger] vals[idx] <= 1_000_000_000,
            decreases vals.len() - k,
        {
            let v = vals[k];
            if v < 0 {
                vals.set(k, -v);
            }
            k += 1;
        }
    } else if mutation_kind == 5 {
        // negate each element
        let mut k: usize = 0;
        while k < vals.len()
            invariant
                vals.len() == rows * cols,
                0 <= k <= vals.len(),
                forall|idx: int| 0 <= idx < k ==> -1_000_000_000 <= #[trigger] vals[idx] <= 1_000_000_000,
                forall|idx: int| k <= idx < vals.len() ==> -1_000_000_000 <= #[trigger] vals[idx] <= 1_000_000_000,
            decreases vals.len() - k,
        {
            let v = vals[k];
            vals.set(k, -v);
            k += 1;
        }
    } else if mutation_kind == 6 && vals.len() > 0 {
        // nudge first element up (if < max)
        if vals[0] < 1_000_000_000 {
            vals.set(0, vals[0] + 1);
        }
    } else if mutation_kind == 7 && vals.len() > 0 {
        // nudge first element down (if > min)
        if vals[0] > -1_000_000_000 {
            vals.set(0, vals[0] - 1);
        }
    }
    // else: identity (mutation_kind == 0 or fallback)

    assert(forall|k: int| 0 <= k < vals.len() ==> -1_000_000_000 <= #[trigger] vals[k] <= 1_000_000_000);

    // Reshape flat array into rows×cols grid
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut ri: usize = 0;
    while ri < rows
        invariant
            1 <= rows <= 1_000,
            1 <= cols <= 1_000,
            rows * cols <= 100_000,
            vals.len() == rows * cols,
            grid.len() == ri,
            0 <= ri <= rows,
            forall|k: int| 0 <= k < vals.len() ==> -1_000_000_000 <= #[trigger] vals[k] <= 1_000_000_000,
            forall|r: int| 0 <= r < ri ==> (#[trigger] grid[r]).len() == cols,
            forall|r: int, c: int| 0 <= r < ri && 0 <= c < cols
                ==> -1_000_000_000 <= #[trigger] grid[r][c] <= 1_000_000_000,
        decreases rows - ri,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut cj: usize = 0;
        while cj < cols
            invariant
                1 <= cols <= 1_000,
                1 <= rows <= 1_000,
                0 <= ri < rows,
                0 <= cj <= cols,
                row.len() == cj,
                vals.len() == rows * cols,
                rows * cols <= 100_000,
                forall|k: int| 0 <= k < vals.len() ==> -1_000_000_000 <= #[trigger] vals[k] <= 1_000_000_000,
                forall|c: int| 0 <= c < cj ==> -1_000_000_000 <= #[trigger] row[c] <= 1_000_000_000,
            decreases cols - cj,
        {
            assert(ri * cols + cj < rows * cols) by(nonlinear_arith)
                requires ri < rows, cj < cols, rows >= 1, cols >= 1;
            row.push(vals[ri * cols + cj]);
            cj += 1;
        }
        assert(row.len() == cols);
        grid.push(row);
        ri += 1;
    }

    assert(grid.len() == rows);

    proof {
        assert(grid.len() >= 1);
        assert forall|r: int| 0 <= r < grid.len() implies (#[trigger] grid[r]).len() == grid[0].len() by {
            assert(grid[r].len() == cols);
            assert(grid[0].len() == cols);
        };
        assert(grid[0].len() == cols);
        assert(grid.len() * grid[0].len() == rows * cols) by {
            assert(grid.len() == rows);
            assert(grid[0].len() == cols);
        };
    }

    grid
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

fn random_flat_values(rng: &mut Rng, count: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut vals = Vec::with_capacity(count);
    for _ in 0..count {
        vals.push(rng.gen_range_i64(lo, hi) as i32);
    }
    vals
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(867);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |matrix: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= count_target { return; }
        let key = format!("{:?}", matrix);
        if !seen.insert(key) { return; }
        let output = Solution::transpose(matrix.clone());
        writeln!(out, "{}", json!({
            "input": {"matrix": matrix},
            "output": output
        })).unwrap();
        *count += 1;
    };

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    // Example 1: [[1,2,3],[4,5,6],[7,8,9]]
    let ex1_vals: Vec<i32> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    for &mk in &mutation_kinds {
        let m = generate_test_case(3, 3, ex1_vals.clone(), mk);
        emit(m, &mut seen, &mut out, &mut count);
    }

    // Example 2: [[1,2,3],[4,5,6]]
    let ex2_vals: Vec<i32> = vec![1, 2, 3, 4, 5, 6];
    for &mk in &mutation_kinds {
        let m = generate_test_case(2, 3, ex2_vals.clone(), mk);
        emit(m, &mut seen, &mut out, &mut count);
    }

    // Boundary and special configurations
    let configs: Vec<(usize, usize)> = vec![
        (1, 1), (1, 2), (2, 1), (1, 5), (5, 1),
        (2, 2), (3, 3), (5, 5), (10, 10),
        (1, 100), (100, 1), (1, 1000), (1000, 1),
        (10, 100), (100, 10), (50, 50),
        (100, 100), (200, 500), (500, 200),
        (1000, 100), (100, 1000), (316, 316),
    ];

    // Boundary value flat arrays
    let boundary_vals: Vec<i64> = vec![
        0, 1, -1, 1_000_000_000, -1_000_000_000,
        999_999_999, -999_999_999, 42, -42,
    ];

    for &(r, c) in &configs {
        if r * c > 100_000 { continue; }
        if count >= count_target { break; }
        let total = r * c;

        // Boundary fill
        for &bv in &boundary_vals {
            if count >= count_target { break; }
            let vals: Vec<i32> = vec![bv as i32; total];
            let m = generate_test_case(r, c, vals.clone(), 0);
            emit(m, &mut seen, &mut out, &mut count);
        }

        // Random values with mutation
        for &mk in &mutation_kinds {
            if count >= count_target { break; }
            let vals = random_flat_values(&mut rng, total, -1_000_000_000, 1_000_000_000);
            let m = generate_test_case(r, c, vals.clone(), mk);
            emit(m, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random sizes and values
    while count < count_target {
        let r = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let max_c = (100_000 / r).min(1000);
        if max_c < 1 { continue; }
        let c = rng.gen_range_usize(1, max_c);
        let total = r * c;
        let mk = (rng.next_u64() % 6) as u8;

        // Mix boundary values in ~20% of elements
        let vals: Vec<i32> = (0..total).map(|i| {
            if i % 5 == 0 {
                let bv_idx = rng.gen_range_usize(0, boundary_vals.len() - 1);
                boundary_vals[bv_idx] as i32
            } else {
                rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32
            }
        }).collect();

        let m = generate_test_case(r, c, vals.clone(), mk);
        emit(m, &mut seen, &mut out, &mut count);
    }
}
