use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<Vec<i32>>) -> (grid: Vec<Vec<i32>>)
    ensures
        1 <= grid.len() <= 100,
        forall|r: int| 0 <= r < grid.len() ==> 1 <= #[trigger] grid[r].len() <= 100,
        forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall|r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> -100 <= #[trigger] grid[r][c] <= 100,
        forall|r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() - 1 ==> #[trigger] grid[r][c] >= grid[r][c + 1],
        forall|r: int, c: int| 0 <= r < grid.len() - 1 && 0 <= c < grid[r].len() ==> #[trigger] grid[r][c] >= grid[r + 1][c],
{
    let n = if values.len() < 1 { 1usize } else if values.len() > 100 { 100usize } else { values.len() };
    let width = if values.len() > 0 { values[0].len() } else { 1usize };
    let cols = if width < 1 { 1usize } else if width > 100 { 100usize } else { width };
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r = 0usize;
    while r < n
        invariant
            1 <= n <= 100,
            1 <= cols <= 100,

            0 <= r <= n,
            grid.len() == r,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
            forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < cols ==> -100 <= #[trigger] grid[i][j] <= 100,
            forall|r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() - 1 ==> #[trigger] grid[r][c] >= grid[r][c + 1],
            forall|r: int, c: int| 0 <= r < grid.len() - 1 && 0 <= c < grid[r].len() ==> #[trigger] grid[r][c] >= grid[r + 1][c],
        decreases n - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c = 0usize;
        while c < cols
            invariant
                1 <= n <= 100,
                0 <= r < n,
                1 <= cols <= 100,
                0 <= c <= cols,
                row.len() == c,
                grid.len() == r,
                forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
                forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < cols ==> -100 <= #[trigger] grid[i][j] <= 100,
                forall|j: int| 0 <= j < row.len() ==> -100 <= #[trigger] row[j] <= 100,
                forall|j: int| 0 <= j < row.len() - 1 ==> #[trigger] row[j] >= row[j + 1],
                forall|j: int| r > 0 && 0 <= j < row.len() ==> grid[r - 1][j] >= #[trigger] row[j],
            decreases cols - c,
        {
            let value = if r < values.len() && c < values[r].len() { values[r][c] } else { -100 };
            let mut value = if value < -100 { -100 } else if value > 100 { 100 } else { value };
            if c > 0 && value > row[c - 1] { value = row[c - 1]; }
            if r > 0 {
                assert(grid[(r - 1) as int].len() == cols);
                let previous = &grid[r - 1];
                if value > previous[c] { value = previous[c]; }
            }
            row.push(value);
            c += 1;
        }
        grid.push(row);
        r += 1;
    }
    grid
}


pub fn generate_candidate(rows: usize, cols: usize, fill_val: i32, corner_val: i32, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= rows <= 100,
        1 <= cols <= 100,
        -100 <= fill_val <= 100,
        -100 <= corner_val <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|r: int| 0 <= r < result.len() ==> 1 <= #[trigger] result[r].len() <= 100,
        forall|r: int| 0 <= r < result.len() ==> #[trigger] result[r].len() == result[0].len(),
        forall|r: int, c: int| 0 <= r < result.len() && 0 <= c < result[r].len() ==> -100 <= #[trigger] result[r][c] <= 100,
{
    // Determine the value for position [0][0] based on mutation_kind
    let v00: i32 = if mutation_kind == 0 {
        fill_val                              // identity
    } else if mutation_kind == 1 {
        -100                                  // min boundary
    } else if mutation_kind == 2 {
        100                                   // max boundary
    } else if mutation_kind == 3 {
        0                                     // zero
    } else if mutation_kind == 4 && fill_val < 100 {
        (fill_val + 1) as i32                 // nudge up
    } else if mutation_kind == 5 && fill_val > -100 {
        (fill_val - 1) as i32                 // nudge down
    } else if mutation_kind == 6 {
        corner_val                            // use corner_val parameter
    } else if mutation_kind == 7 {
        1                                     // positive
    } else if mutation_kind == 8 {
        -1                                    // negative
    } else {
        fill_val                              // fallback
    };

    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r <= rows,
            1 <= rows <= 100,
            1 <= cols <= 100,
            -100 <= fill_val <= 100,
            -100 <= v00 <= 100,
            grid.len() == r,
            forall|i: int| 0 <= i < r ==> #[trigger] grid[i].len() == cols,
            forall|i: int, j: int| 0 <= i < r && 0 <= j < grid[i].len()
                ==> -100 <= #[trigger] grid[i][j] <= 100,
        decreases rows - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= c <= cols,
                1 <= cols <= 100,
                -100 <= fill_val <= 100,
                -100 <= v00 <= 100,
                r < rows,
                row.len() == c,
                forall|j: int| 0 <= j < c ==> -100 <= #[trigger] row[j] <= 100,
            decreases cols - c,
        {
            if r == 0 && c == 0 {
                row.push(v00);
            } else {
                row.push(fill_val);
            }
            c += 1;
        }
        grid.push(row);
        r += 1;
    }
    grid
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

fn gen(rows: usize, cols: usize, fill_val: i32, corner_val: i32, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_candidate(rows, cols, fill_val, corner_val, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_grid(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    let mut grid = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for _ in 0..cols {
            row.push(rng.gen_range_i64(-100, 100) as i32);
        }
        grid.push(row);
    }
    grid
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1351);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let grid = generate_test_case(grid);
        if *count >= target { return; }
        let key = format!("{:?}", grid);
        if !seen.insert(key) { return; }
        let output = Solution::count_negatives(grid.clone());
        writeln!(out, "{}", json!({"input": {"grid": grid}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from problem description
    emit(vec![vec![4,3,2,-1], vec![3,2,1,-1], vec![1,1,-1,-2], vec![-1,-1,-2,-3]], &mut seen, &mut out, &mut count);
    emit(vec![vec![3,2], vec![1,0]], &mut seen, &mut out, &mut count);

    // Generated grids with mutations
    let fill_vals: Vec<i32> = vec![0, -100, 100, -1, 1, 50, -50, 99, -99];
    let corner_vals: Vec<i32> = vec![0, -100, 100, -1, 1, -50, 50];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];
    let sizes: Vec<(usize, usize)> = vec![(1,1), (1,2), (2,1), (2,2), (3,3), (1,100), (100,1), (10,10)];

    for &(rows, cols) in &sizes {
        for &fv in &fill_vals {
            for &mk in &mutation_kinds {
                let cv = corner_vals[mk as usize % corner_vals.len()];
                let result = gen(rows, cols, fv, cv, mk);
                emit(result, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random grids for extra diversity
    while count < target {
        let rows = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(1, 20),
            3 => rng.gen_range_usize(20, 50),
            _ => rng.gen_range_usize(50, 100),
        };
        let cols = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(1, 20),
            3 => rng.gen_range_usize(20, 50),
            _ => rng.gen_range_usize(50, 100),
        };
        let grid = random_grid(&mut rng, rows, cols);
        emit(grid, &mut seen, &mut out, &mut count);
    }
}
