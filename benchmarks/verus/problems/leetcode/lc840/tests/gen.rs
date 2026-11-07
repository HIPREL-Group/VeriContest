use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw: Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= raw.len() <= 10,
        1 <= raw[0].len() <= 10,
        forall|i: int| 0 <= i < raw.len() ==> #[trigger] raw[i].len() == raw[0].len(),
    ensures
        1 <= grid.len() <= 10,
        1 <= grid[0].len() <= 10,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall|i: int, j: int|
            0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 15,
{
    let cols = raw[0].len();
    let rows = raw.len();
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r <= rows,
            grid.len() == r,
            rows == raw.len(),
            cols == raw[0].len(),
            1 <= rows <= 10,
            1 <= cols <= 10,
            forall|i: int| 0 <= i < raw.len() ==> #[trigger] raw[i].len() == cols,
            forall|i: int| 0 <= i < r as int ==> (#[trigger] grid[i]).len() == cols,
            forall|i: int, j: int|
                0 <= i < r as int && 0 <= j < cols as int
                    ==> 0 <= #[trigger] grid[i][j] <= 15,
        decreases rows - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= c <= cols,
                row.len() == c,
                1 <= cols <= 10,
                r < rows,
                rows == raw.len(),
                cols == raw[0].len(),
                forall|i: int| 0 <= i < raw.len() ==> #[trigger] raw[i].len() == cols,
                forall|j: int| 0 <= j < c as int ==> 0 <= #[trigger] row[j] <= 15,
            decreases cols - c,
        {
            assert(raw[r as int].len() == cols);
            let v = raw[r][c];
            let clamped: i32 = if v < 0 { 0i32 } else if v > 15 { 15i32 } else { v };

            let val: i32 = if mutation_kind == 1 {
                // all zeros
                0i32
            } else if mutation_kind == 2 {
                // all max
                15i32
            } else if mutation_kind == 3 && r == 0 && c == 0 {
                // set [0][0] to 0
                0i32
            } else if mutation_kind == 4 && r == 0 && c == 0 {
                // set [0][0] to 15
                15i32
            } else if mutation_kind == 5 && r == 0 && c == 0 && clamped < 15 {
                // nudge [0][0] up
                (clamped + 1) as i32
            } else if mutation_kind == 6 && r == 0 && c == 0 && clamped > 0 {
                // nudge [0][0] down
                (clamped - 1) as i32
            } else if mutation_kind == 7 {
                // set all to 5 (middle value)
                5i32
            } else {
                // identity (clamped)
                clamped
            };
            row.push(val);
            c = c + 1;
        }
        grid.push(row);
        r = r + 1;
    }
    proof {
        assert(grid.len() == rows);
        assert(rows >= 1);
        assert(grid[0].len() == cols);
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

extern crate serde_json;
use serde_json::json;

fn random_grid(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    let mut grid = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for _ in 0..cols {
            row.push(rng.gen_range_i64(0, 15) as i32);
        }
        grid.push(row);
    }
    grid
}

fn grid_with_magic_at(rng: &mut Rng, rows: usize, cols: usize, mr: usize, mc: usize) -> Vec<Vec<i32>> {
    // All 3x3 magic squares using 1-9 with magic constant 15.
    // There are 8 such squares (rotations/reflections of one base).
    let magic_squares: [[i32; 9]; 8] = [
        [2, 7, 6, 9, 5, 1, 4, 3, 8],
        [6, 1, 8, 7, 5, 3, 2, 9, 4],
        [8, 3, 4, 1, 5, 9, 6, 7, 2],
        [4, 9, 2, 3, 5, 7, 8, 1, 6],
        [2, 9, 4, 7, 5, 3, 6, 1, 8],
        [4, 3, 8, 9, 5, 1, 2, 7, 6],
        [8, 1, 6, 3, 5, 7, 4, 9, 2],
        [6, 7, 2, 1, 5, 9, 8, 3, 4],
    ];
    let idx = rng.gen_range_usize(0, 7);
    let ms = &magic_squares[idx];
    let mut grid = random_grid(rng, rows, cols);
    for dr in 0..3 {
        for dc in 0..3 {
            grid[mr + dr][mc + dc] = ms[dr * 3 + dc];
        }
    }
    grid
}

fn mutate(raw: Vec<Vec<i32>>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(raw, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(840);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, n: &mut usize| {
        if *n >= count { return; }
        let key = format!("{:?}", grid);
        if !seen.insert(key) { return; }
        let output = Solution::num_magic_squares_inside(grid.clone());
        writeln!(out, "{}", json!({"input": {"grid": grid}, "output": output})).unwrap();
        *n += 1;
    };

    // Example 1 from description
    let ex1 = vec![
        vec![4, 3, 8, 4],
        vec![9, 5, 1, 9],
        vec![2, 7, 6, 2],
    ];
    emit(mutate(ex1, 0), &mut seen, &mut out, &mut n);

    // Example 2 from description
    let ex2 = vec![vec![8]];
    emit(mutate(ex2, 0), &mut seen, &mut out, &mut n);

    // Grids too small for any magic square
    let small_grids: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1, 2], vec![3, 4]],
        vec![vec![5]],
        vec![vec![1, 2, 3]],
        vec![vec![1], vec![2], vec![3]],
    ];
    for g in small_grids {
        emit(mutate(g, 0), &mut seen, &mut out, &mut n);
    }

    // 3x3 grids that ARE magic squares
    let magic_3x3: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![2, 7, 6], vec![9, 5, 1], vec![4, 3, 8]],
        vec![vec![6, 1, 8], vec![7, 5, 3], vec![2, 9, 4]],
    ];
    for g in &magic_3x3 {
        for mk in 0u8..=8 {
            emit(mutate(g.clone(), mk), &mut seen, &mut out, &mut n);
        }
    }

    // Larger grids with embedded magic squares
    for _ in 0..10 {
        let rows = rng.gen_range_usize(3, 10);
        let cols = rng.gen_range_usize(3, 10);
        let mr = rng.gen_range_usize(0, rows - 3);
        let mc = rng.gen_range_usize(0, cols - 3);
        let g = grid_with_magic_at(&mut rng, rows, cols, mr, mc);
        for mk in [0u8, 1, 2, 7] {
            emit(mutate(g.clone(), mk), &mut seen, &mut out, &mut n);
        }
    }

    // Max-size grids (10x10)
    for _ in 0..5 {
        let g = random_grid(&mut rng, 10, 10);
        emit(mutate(g, 0), &mut seen, &mut out, &mut n);
    }
    for _ in 0..3 {
        let mr = rng.gen_range_usize(0, 7);
        let mc = rng.gen_range_usize(0, 7);
        let g = grid_with_magic_at(&mut rng, 10, 10, mr, mc);
        emit(mutate(g, 0), &mut seen, &mut out, &mut n);
    }

    // Random grids with all mutation kinds
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];
    while n < count {
        let rows = match n % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, 3),
            2 => rng.gen_range_usize(3, 5),
            3 => rng.gen_range_usize(5, 8),
            _ => rng.gen_range_usize(8, 10),
        };
        let cols = match n % 4 {
            0 => 1,
            1 => rng.gen_range_usize(1, 3),
            2 => rng.gen_range_usize(3, 7),
            _ => rng.gen_range_usize(7, 10),
        };
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let g = if rows >= 3 && cols >= 3 && rng.gen_range_usize(0, 1) == 0 {
            let mr = rng.gen_range_usize(0, rows - 3);
            let mc = rng.gen_range_usize(0, cols - 3);
            grid_with_magic_at(&mut rng, rows, cols, mr, mc)
        } else {
            random_grid(&mut rng, rows, cols)
        };
        emit(mutate(g, mk), &mut seen, &mut out, &mut n);
    }
}
