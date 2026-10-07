use vstd::prelude::*;

verus! {

/// Build an n×n grid of i32 values in [0, 50] from a flat vector of cell values.
/// Construction parameters:
///   - n: grid side length (1..=50)
///   - cells: flat Vec of length n*n with values in [0, 50]
///   - mutation_kind: selects structural mutations on the constructed grid
pub fn generate_test_case(
    n: usize,
    cells: Vec<i32>,
    mutation_kind: u8,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= n <= 50,
        cells.len() == n * n,
        forall|k: int| 0 <= k < cells.len() ==> 0 <= #[trigger] cells[k] <= 50,
    ensures
        1 <= grid.len() <= 50,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
        forall|i: int, j: int|
            0 <= i < grid.len() && 0 <= j < grid.len() ==> 0 <= #[trigger] grid[i][j] <= 50,
{
    // Build base grid row by row
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < n
        invariant
            0 <= r <= n,
            1 <= n <= 50,
            grid.len() == r,
            cells.len() == n * n,
            forall|k: int| 0 <= k < cells.len() ==> 0 <= #[trigger] cells[k] <= 50,
            forall|i: int| 0 <= i < r as int ==> #[trigger] grid[i].len() == n,
            forall|i: int, j: int|
                0 <= i < r as int && 0 <= j < n as int
                    ==> 0 <= #[trigger] grid[i][j] <= 50,
        decreases n - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < n
            invariant
                0 <= c <= n,
                1 <= n <= 50,
                r < n,
                row.len() == c,
                cells.len() == n * n,
                forall|k: int| 0 <= k < cells.len() ==> 0 <= #[trigger] cells[k] <= 50,
                forall|j: int| 0 <= j < c as int ==> 0 <= #[trigger] row[j] <= 50,
            decreases n - c,
        {
            assert(0 <= r * n + c < n * n) by {
                assert(r < n);
                assert(c < n);
                assert(r * n + c < n * n) by(nonlinear_arith)
                    requires r < n, c < n, n >= 1
                {}
            }
            let idx = r * n + c;
            row.push(cells[idx]);
            c += 1;
        }
        grid.push(row);
        r += 1;
    }

    // Apply mutations
    if mutation_kind == 0 {
        // identity
        grid
    } else if mutation_kind == 1 {
        // set all cells to 0
        let mut g = grid;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 50,
                g.len() == n,
                forall|r: int| 0 <= r < n as int ==> #[trigger] g[r].len() == n,
                forall|r: int, c: int|
                    0 <= r < i as int && 0 <= c < n as int
                        ==> #[trigger] g[r][c] == 0,
                forall|r: int, c: int|
                    i as int <= r < n as int && 0 <= c < n as int
                        ==> 0 <= #[trigger] g[r][c] <= 50,
            decreases n - i,
        {
            let mut j: usize = 0;
            let mut row = g[i].clone();
            while j < n
                invariant
                    0 <= j <= n,
                    1 <= n <= 50,
                    row.len() == n,
                    forall|c: int| 0 <= c < j as int ==> #[trigger] row[c] == 0,
                    forall|c: int| j as int <= c < n as int ==> 0 <= #[trigger] row[c] <= 50,
                decreases n - j,
            {
                row.set(j, 0);
                j += 1;
            }
            g.set(i, row);
            i += 1;
        }
        g
    } else if mutation_kind == 2 {
        // set all cells to 50 (max value)
        let mut g = grid;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 50,
                g.len() == n,
                forall|r: int| 0 <= r < n as int ==> #[trigger] g[r].len() == n,
                forall|r: int, c: int|
                    0 <= r < i as int && 0 <= c < n as int
                        ==> #[trigger] g[r][c] == 50,
                forall|r: int, c: int|
                    i as int <= r < n as int && 0 <= c < n as int
                        ==> 0 <= #[trigger] g[r][c] <= 50,
            decreases n - i,
        {
            let mut j: usize = 0;
            let mut row = g[i].clone();
            while j < n
                invariant
                    0 <= j <= n,
                    1 <= n <= 50,
                    row.len() == n,
                    forall|c: int| 0 <= c < j as int ==> #[trigger] row[c] == 50,
                    forall|c: int| j as int <= c < n as int ==> 0 <= #[trigger] row[c] <= 50,
                decreases n - j,
            {
                row.set(j, 50);
                j += 1;
            }
            g.set(i, row);
            i += 1;
        }
        g
    } else if mutation_kind == 3 && n >= 2 {
        // set first cell to 0
        let mut g = grid;
        let mut row0 = g[0].clone();
        row0.set(0, 0);
        g.set(0, row0);
        g
    } else if mutation_kind == 4 && n >= 2 {
        // set first cell to 50
        let mut g = grid;
        let mut row0 = g[0].clone();
        row0.set(0, 50);
        g.set(0, row0);
        g
    } else if mutation_kind == 5 {
        // set diagonal to 0
        let mut g = grid;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 50,
                g.len() == n,
                forall|r: int| 0 <= r < n as int ==> #[trigger] g[r].len() == n,
                forall|r: int, c: int|
                    0 <= r < n as int && 0 <= c < n as int
                        ==> 0 <= #[trigger] g[r][c] <= 50,
            decreases n - i,
        {
            let mut row = g[i].clone();
            row.set(i, 0);
            g.set(i, row);
            i += 1;
        }
        g
    } else {
        // fallback: identity
        grid
    }
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

fn build_grid(n: usize, cells: Vec<i32>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(n, cells, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_cells(rng: &mut Rng, count: usize, val_lo: i64, val_hi: i64) -> Vec<i32> {
    let mut cells = Vec::with_capacity(count);
    for _ in 0..count {
        cells.push(rng.gen_range_i64(val_lo, val_hi) as i32);
    }
    cells
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(892);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", grid);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::surface_area(grid.clone());
        let grid_json: Vec<Vec<i32>> = grid;
        writeln!(out, "{}", json!({"input": {"grid": grid_json}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1, 2], vec![3, 4]],
        vec![vec![1, 1, 1], vec![1, 0, 1], vec![1, 1, 1]],
        vec![vec![2, 2, 2], vec![2, 1, 2], vec![2, 2, 2]],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Edge cases: 1x1 grids
    for v in [0, 1, 25, 50] {
        let grid = build_grid(1, vec![v], 0);
        emit(grid, &mut seen, &mut out, &mut count);
    }

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    // Seed grids × mutations
    let seed_sizes: Vec<usize> = vec![2, 3, 4, 5];
    for &n in &seed_sizes {
        for &mk in &mutation_kinds {
            let cells = random_cells(&mut rng, n * n, 0, 50);
            let grid = build_grid(n, cells, mk);
            emit(grid, &mut seen, &mut out, &mut count);
        }
    }

    // Diverse sizes with random mutations
    for i in 0..80 {
        if count >= target_count { break; }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(2, 5),        // small
            2 => rng.gen_range_usize(6, 15),       // medium
            3 => rng.gen_range_usize(16, 30),      // large
            _ => rng.gen_range_usize(31, 50),      // max
        };
        let val_lo: i64 = if i % 4 == 0 { 0 } else { 0 };
        let val_hi: i64 = match i % 5 {
            0 => 1,
            1 => 5,
            2 => 10,
            3 => 25,
            _ => 50,
        };
        let cells = random_cells(&mut rng, n * n, val_lo, val_hi);
        let mk = (rng.next_u64() % 6) as u8;
        let grid = build_grid(n, cells, mk);
        emit(grid, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random grids
    while count < target_count {
        let n = rng.gen_range_usize(1, 50);
        let cells = random_cells(&mut rng, n * n, 0, 50);
        let mk = (rng.next_u64() % 6) as u8;
        let grid = build_grid(n, cells, mk);
        emit(grid, &mut seen, &mut out, &mut count);
    }
}
