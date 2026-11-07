use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    grid: Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        2 <= grid.len() <= 50,
        2 <= grid[0].len() <= 50,
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int|
            0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 2500,
    ensures
        2 <= result.len() <= 50,
        2 <= result[0].len() <= 50,
        forall |r: int| 0 <= r < result.len() ==> #[trigger] result[r].len() == result[0].len(),
        forall |r: int, c: int|
            0 <= r < result.len() && 0 <= c < result[r].len() ==> 1 <= #[trigger] result[r][c] <= 2500,
{
    if mutation_kind == 0 {
        // identity
        grid
    } else if mutation_kind == 1 || mutation_kind == 2 {
        // construct all-same-value grid: 1 (min) or 2500 (max)
        let fill: i32 = if mutation_kind == 1 { 1 } else { 2500 };
        let rows = grid.len();
        let cols = grid[0].len();
        let mut res: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                2 <= rows <= 50,
                2 <= cols <= 50,
                fill == 1 || fill == 2500,
                res.len() == i as nat,
                forall|r: int| 0 <= r < i as int ==> (#[trigger] res[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int
                    ==> 1 <= #[trigger] res[r][c] <= 2500,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    2 <= cols <= 50,
                    fill == 1 || fill == 2500,
                    row.len() == j as nat,
                    forall|c: int| 0 <= c < j as int ==> 1 <= #[trigger] row[c] <= 2500,
                decreases cols - j,
            {
                row.push(fill);
                j += 1;
            }
            res.push(row);
            i += 1;
        }
        res
    } else if mutation_kind == 3 {
        // construct diagonal-highlight grid: cells on the diagonal get 2500, rest get 1
        let rows = grid.len();
        let cols = grid[0].len();
        let mut res: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                2 <= rows <= 50,
                2 <= cols <= 50,
                res.len() == i as nat,
                forall|r: int| 0 <= r < i as int ==> (#[trigger] res[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int
                    ==> 1 <= #[trigger] res[r][c] <= 2500,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    2 <= cols <= 50,
                    0 <= i < rows,
                    2 <= rows <= 50,
                    row.len() == j as nat,
                    forall|c: int| 0 <= c < j as int ==> 1 <= #[trigger] row[c] <= 2500,
                decreases cols - j,
            {
                let val: i32 = if j == i { 2500 } else { 1 };
                row.push(val);
                j += 1;
            }
            res.push(row);
            i += 1;
        }
        res
    } else if mutation_kind == 4 {
        // construct checkerboard: alternating 1 and 2500
        let rows = grid.len();
        let cols = grid[0].len();
        let mut res: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                2 <= rows <= 50,
                2 <= cols <= 50,
                res.len() == i as nat,
                forall|r: int| 0 <= r < i as int ==> (#[trigger] res[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int
                    ==> 1 <= #[trigger] res[r][c] <= 2500,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    2 <= cols <= 50,
                    0 <= i < rows,
                    2 <= rows <= 50,
                    row.len() == j as nat,
                    forall|c: int| 0 <= c < j as int ==> 1 <= #[trigger] row[c] <= 2500,
                decreases cols - j,
            {
                let val: i32 = if (i + j) % 2 == 0 { 1 } else { 2500 };
                row.push(val);
                j += 1;
            }
            res.push(row);
            i += 1;
        }
        res
    } else if mutation_kind == 5 {
        // construct row-gradient: each row has the same value = row_index + 1
        let rows = grid.len();
        let cols = grid[0].len();
        let mut res: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                2 <= rows <= 50,
                2 <= cols <= 50,
                res.len() == i as nat,
                forall|r: int| 0 <= r < i as int ==> (#[trigger] res[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int
                    ==> 1 <= #[trigger] res[r][c] <= 2500,
            decreases rows - i,
        {
            let row_val: i32 = (i as i32) + 1;
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    2 <= cols <= 50,
                    1 <= row_val <= 50,
                    row.len() == j as nat,
                    forall|c: int| 0 <= c < j as int ==> 1 <= #[trigger] row[c] <= 2500,
                decreases cols - j,
            {
                row.push(row_val);
                j += 1;
            }
            res.push(row);
            i += 1;
        }
        res
    } else {
        // fallback: identity
        grid
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

fn random_grid(rng: &mut Rng, m: usize, n: usize) -> Vec<Vec<i32>> {
    let mut grid = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_i64(1, 2500) as i32);
        }
        grid.push(row);
    }
    grid
}

fn all_val_grid(m: usize, n: usize, val: i32) -> Vec<Vec<i32>> {
    let mut grid = Vec::with_capacity(m);
    for _ in 0..m {
        grid.push(vec![val; n]);
    }
    grid
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3417);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", grid);
        if !seen.insert(key) { return; }
        let output = Solution::zigzag_traversal(grid.clone());
        writeln!(out, "{}", json!({"input": {"grid": grid}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let ex1 = vec![vec![1, 2], vec![3, 4]];
    let ex2 = vec![vec![2, 1], vec![2, 1], vec![2, 1]];
    let ex3 = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
    emit(ex1, &mut seen, &mut out, &mut count);
    emit(ex2, &mut seen, &mut out, &mut count);
    emit(ex3, &mut seen, &mut out, &mut count);

    // Structured seed grids with all mutation kinds
    let seed_grids: Vec<Vec<Vec<i32>>> = vec![
        // 2x2 patterns
        vec![vec![1, 1], vec![1, 1]],
        vec![vec![2500, 2500], vec![2500, 2500]],
        vec![vec![1, 2500], vec![2500, 1]],
        // 2x3
        vec![vec![1, 2, 3], vec![4, 5, 6]],
        // 3x2
        vec![vec![1, 2], vec![3, 4], vec![5, 6]],
        // 3x3
        all_val_grid(3, 3, 1),
        all_val_grid(3, 3, 2500),
        vec![vec![1, 2, 3], vec![6, 5, 4], vec![7, 8, 9]],
        // 4x4 sequential
        vec![vec![1, 2, 3, 4], vec![5, 6, 7, 8], vec![9, 10, 11, 12], vec![13, 14, 15, 16]],
        // 2x5 (wide)
        vec![vec![1, 2, 3, 4, 5], vec![6, 7, 8, 9, 10]],
        // 5x2 (tall)
        vec![vec![1, 2], vec![3, 4], vec![5, 6], vec![7, 8], vec![9, 10]],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    for mat in &seed_grids {
        for &mk in &mutation_kinds {
            let result = generate_test_case(mat.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random grids across size classes
    let mut _attempts_0 = 0usize;
    while count < target_count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let (m, n) = match count % 5 {
            0 => (2, 2),                                                       // minimum
            1 => (rng.gen_range_usize(2, 5), rng.gen_range_usize(2, 5)),       // tiny
            2 => (rng.gen_range_usize(5, 15), rng.gen_range_usize(5, 15)),     // medium
            3 => (rng.gen_range_usize(15, 35), rng.gen_range_usize(15, 35)),   // large
            _ => (rng.gen_range_usize(35, 50), rng.gen_range_usize(35, 50)),   // max
        };

        let grid = if count % 10 == 0 {
            all_val_grid(m, n, 1)
        } else if count % 10 == 5 {
            all_val_grid(m, n, 2500)
        } else {
            random_grid(&mut rng, m, n)
        };

        let mk = rng.gen_range_usize(0, 5) as u8;
        let result = generate_test_case(grid, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
