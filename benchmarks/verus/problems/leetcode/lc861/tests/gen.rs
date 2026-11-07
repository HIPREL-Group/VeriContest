use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    cells: Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= cells.len() <= 20,
        1 <= cells[0].len() <= 20,
        forall|r: int| 0 <= r < cells.len() ==> #[trigger] cells[r].len() == cells[0].len(),
        forall|r: int, c: int|
            0 <= r < cells.len() && 0 <= c < cells[0].len() ==> 0 <= #[trigger] cells[r][c] <= 1,
    ensures
        1 <= result.len() <= 20,
        1 <= result[0].len() <= 20,
        forall|r: int| 0 <= r < result.len() ==> #[trigger] result[r].len() == result[0].len(),
        forall|r: int, c: int|
            0 <= r < result.len() && 0 <= c < result[0].len() ==> 0 <= #[trigger] result[r][c] <= 1,
{
    if mutation_kind == 0 {
        // identity
        cells
    } else if mutation_kind == 1 {
        // set all cells to 0
        let rows = cells.len();
        let cols = cells[0].len();
        let mut grid: Vec<Vec<i32>> = Vec::new();
        let mut r: usize = 0;
        while r < rows
            invariant
                0 <= r <= rows,
                rows == cells.len(),
                cols == cells[0].len(),
                1 <= rows <= 20,
                1 <= cols <= 20,
                grid.len() == r as int,
                forall|i: int| 0 <= i < r ==> #[trigger] grid[i].len() == cols,
                forall|i: int, j: int|
                    0 <= i < r && 0 <= j < cols ==> #[trigger] grid[i][j] == 0,
            decreases rows - r,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < cols
                invariant
                    0 <= c <= cols,
                    1 <= cols <= 20,
                    row.len() == c as int,
                    forall|j: int| 0 <= j < c ==> #[trigger] row[j] == 0,
                decreases cols - c,
            {
                row.push(0);
                c += 1;
            }
            grid.push(row);
            r += 1;
        }
        grid
    } else if mutation_kind == 2 {
        // set all cells to 1
        let rows = cells.len();
        let cols = cells[0].len();
        let mut grid: Vec<Vec<i32>> = Vec::new();
        let mut r: usize = 0;
        while r < rows
            invariant
                0 <= r <= rows,
                rows == cells.len(),
                cols == cells[0].len(),
                1 <= rows <= 20,
                1 <= cols <= 20,
                grid.len() == r as int,
                forall|i: int| 0 <= i < r ==> #[trigger] grid[i].len() == cols,
                forall|i: int, j: int|
                    0 <= i < r && 0 <= j < cols ==> #[trigger] grid[i][j] == 1,
            decreases rows - r,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < cols
                invariant
                    0 <= c <= cols,
                    1 <= cols <= 20,
                    row.len() == c as int,
                    forall|j: int| 0 <= j < c ==> #[trigger] row[j] == 1,
                decreases cols - c,
            {
                row.push(1);
                c += 1;
            }
            grid.push(row);
            r += 1;
        }
        grid
    } else if mutation_kind == 3 {
        // flip the first cell: toggle cells[0][0]
        let mut grid = cells;
        let mut row0 = grid.remove(0);
        let old = row0[0];
        let new_val: i32 = if old == 0 { 1 } else { 0 };
        row0.set(0, new_val);
        grid.insert(0, row0);
        grid
    } else if mutation_kind == 4 {
        // flip all cells in the first row
        let mut grid = cells;
        let mut row0 = grid.remove(0);
        let cols = row0.len();
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= c <= cols,
                cols == row0.len(),
                1 <= cols <= 20,
                forall|j: int| 0 <= j < c ==> 0 <= #[trigger] row0[j] <= 1,
                forall|j: int| c <= j < cols ==> 0 <= #[trigger] row0[j] <= 1,
            decreases cols - c,
        {
            let old = row0[c];
            let new_val: i32 = if old == 0 { 1 } else { 0 };
            row0.set(c, new_val);
            c += 1;
        }
        grid.insert(0, row0);
        grid
    } else if mutation_kind == 5 && cells.len() >= 2 {
        // swap first two rows
        let mut grid = cells;
        let row0 = grid.remove(0);
        let row1 = grid.remove(0);
        grid.insert(0, row0);
        grid.insert(0, row1);
        grid
    } else {
        // fallback: identity
        cells
    }
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let range = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % range) as i64) as i32
    }
}

struct Solution;
include!("../code.rs");

fn make_grid(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    let mut grid = Vec::new();
    for _ in 0..rows {
        let mut row = Vec::new();
        for _ in 0..cols {
            row.push(rng.gen_range_i32(0, 1));
        }
        grid.push(row);
    }
    grid
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    // Example test cases from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![0,0,1,1], vec![1,0,1,0], vec![1,1,0,0]],
        vec![vec![0]],
    ];

    let mut generated = 0usize;

    for ex in &examples {
        let grid = ex.clone();
        let result = Solution::matrix_score(grid.clone());
        writeln!(out, "{}", json!({
            "input": {"grid": grid},
            "output": result
        })).unwrap();
        generated += 1;
    }

    let num_mutations: u8 = 6;

    while generated < count {
        // Size classes for rows and cols
        let rows: usize = match generated % 5 {
            0 => 1,                                    // minimum
            1 => rng.gen_range_usize(1, 3),            // tiny
            2 => rng.gen_range_usize(4, 10),           // small
            3 => rng.gen_range_usize(11, 15),          // medium
            _ => rng.gen_range_usize(16, 20),          // max range
        };
        let cols: usize = match generated % 7 {
            0 => 1,                                    // minimum
            1 => rng.gen_range_usize(1, 3),            // tiny
            2 => rng.gen_range_usize(4, 10),           // small
            3 => rng.gen_range_usize(11, 15),          // medium
            4 => 20,                                   // maximum
            5 => rng.gen_range_usize(1, 20),           // full range
            _ => rng.gen_range_usize(5, 12),           // mid range
        };

        let base_grid = make_grid(&mut rng, rows, cols);
        let mutation = (rng.next_u64() % num_mutations as u64) as u8;

        let grid = generate_test_case(base_grid, mutation);
        let result = Solution::matrix_score(grid.clone());
        writeln!(out, "{}", json!({
            "input": {"grid": grid},
            "output": result
        })).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
