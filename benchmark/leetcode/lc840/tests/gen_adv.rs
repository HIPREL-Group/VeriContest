use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    values: &Vec<Vec<i32>>,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= rows <= 10,
        1 <= cols <= 10,
        values.len() == rows,
        forall|i: int| 0 <= i < values.len() ==> #[trigger] values[i].len() == cols,
        forall|i: int, j: int|
            0 <= i < values.len() && 0 <= j < values[i].len()
                ==> 0 <= #[trigger] values[i][j] <= 15,
    ensures
        1 <= grid.len() <= 10,
        1 <= grid[0].len() <= 10,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall|i: int, j: int|
            0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 15,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < rows
        invariant
            1 <= rows <= 10,
            1 <= cols <= 10,
            values.len() == rows,
            0 <= i <= rows,
            grid.len() == i,
            forall|k: int| 0 <= k < values.len() ==> #[trigger] values[k].len() == cols,
            forall|k: int, j: int|
                0 <= k < values.len() && 0 <= j < values[k].len()
                    ==> 0 <= #[trigger] values[k][j] <= 15,
            forall|k: int| 0 <= k < grid.len() ==> #[trigger] grid[k].len() == cols,
            forall|k: int, j: int|
                0 <= k < grid.len() && 0 <= j < grid[k].len()
                    ==> 0 <= #[trigger] grid[k][j] <= 15,
        decreases rows - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                1 <= cols <= 10,
                0 <= j <= cols,
                row.len() == j,
                i < values.len(),
                values[i as int].len() == cols,
                forall|k: int| 0 <= k < values[i as int].len() ==> 0 <= #[trigger] values[i as int][k] <= 15,
                forall|k: int| 0 <= k < row.len() ==> 0 <= #[trigger] row[k] <= 15,
            decreases cols - j,
        {
            let v = values[i][j];
            assert(0 <= v <= 15);
            row.push(v);
            j += 1;
        }
        grid.push(row);
        i += 1;
    }

    grid
}

}

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

// The canonical magic square (Lo Shu).
const MAGIC: [[i32; 3]; 3] = [
    [4, 9, 2],
    [3, 5, 7],
    [8, 1, 6],
];

// Other magic square rotations/reflections
const MAGIC2: [[i32; 3]; 3] = [
    [2, 7, 6],
    [9, 5, 1],
    [4, 3, 8],
];

const MAGIC3: [[i32; 3]; 3] = [
    [8, 3, 4],
    [1, 5, 9],
    [6, 7, 2],
];

const MAGIC4: [[i32; 3]; 3] = [
    [6, 1, 8],
    [7, 5, 3],
    [2, 9, 4],
];

fn place_magic(grid: &mut Vec<Vec<i32>>, r: usize, c: usize, variant: usize) {
    let m = match variant % 4 {
        0 => &MAGIC,
        1 => &MAGIC2,
        2 => &MAGIC3,
        _ => &MAGIC4,
    };
    for i in 0..3 {
        for j in 0..3 {
            if r + i < grid.len() && c + j < grid[0].len() {
                grid[r + i][c + j] = m[i][j];
            }
        }
    }
}

fn build_grid(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize, Vec<Vec<i32>>) {
    let (rows, cols) = match mode {
        0 => (rng.gen_usize(1, 2), rng.gen_usize(1, 10)), // too small
        1 => (rng.gen_usize(1, 10), rng.gen_usize(1, 2)),
        2 => (3, 3), // exact
        3 => (rng.gen_usize(3, 10), rng.gen_usize(3, 10)),
        4 => (10, 10),
        5 => (3, 10),
        6 => (10, 3),
        7 => (rng.gen_usize(3, 10), rng.gen_usize(3, 10)),
        8 => (rng.gen_usize(3, 10), rng.gen_usize(3, 10)),
        9 => (rng.gen_usize(1, 10), rng.gen_usize(1, 10)),
        _ => (rng.gen_usize(1, 10), rng.gen_usize(1, 10)),
    };

    let mut grid: Vec<Vec<i32>> = vec![vec![0i32; cols]; rows];

    match mode {
        0 | 1 => {
            // small grids, random 0..=15
            for i in 0..rows {
                for j in 0..cols {
                    grid[i][j] = rng.gen_range(0, 15);
                }
            }
        }
        2 => {
            // exact 3x3 magic
            let v = (t as usize) % 4;
            for i in 0..3 {
                for j in 0..3 {
                    let m = match v {
                        0 => &MAGIC,
                        1 => &MAGIC2,
                        2 => &MAGIC3,
                        _ => &MAGIC4,
                    };
                    grid[i][j] = m[i][j];
                }
            }
        }
        3 => {
            // random 1..=9
            for i in 0..rows {
                for j in 0..cols {
                    grid[i][j] = rng.gen_range(1, 9);
                }
            }
        }
        4 => {
            // 10x10 with some magic embedded
            for i in 0..rows {
                for j in 0..cols {
                    grid[i][j] = rng.gen_range(0, 15);
                }
            }
            if rows >= 3 && cols >= 3 {
                let r = rng.gen_usize(0, rows - 3);
                let c = rng.gen_usize(0, cols - 3);
                place_magic(&mut grid, r, c, t);
            }
        }
        5 | 6 => {
            // 3xN or Nx3
            for i in 0..rows {
                for j in 0..cols {
                    grid[i][j] = rng.gen_range(1, 9);
                }
            }
            if rows >= 3 && cols >= 3 {
                place_magic(&mut grid, 0, 0, t);
            }
        }
        7 => {
            // mostly 5s (center magic value)
            for i in 0..rows {
                for j in 0..cols {
                    grid[i][j] = if rng.gen_range(0, 3) == 0 { rng.gen_range(1, 9) } else { 5 };
                }
            }
        }
        8 => {
            // contains values > 9 (should not be magic)
            for i in 0..rows {
                for j in 0..cols {
                    grid[i][j] = rng.gen_range(10, 15);
                }
            }
            if rows >= 3 && cols >= 3 && t % 2 == 0 {
                place_magic(&mut grid, 0, 0, t);
            }
        }
        9 => {
            // all zeros
            for i in 0..rows {
                for j in 0..cols {
                    grid[i][j] = 0;
                }
            }
        }
        _ => {
            // random
            for i in 0..rows {
                for j in 0..cols {
                    grid[i][j] = rng.gen_range(0, 15);
                }
            }
        }
    }

    (rows, cols, grid)
}

fn print_json(grid: &Vec<Vec<i32>>, r: usize, c: usize) {
    let _ = (r, c);
    print!("{{\"grid\":[");
    for i in 0..grid.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..grid[i].len() {
            if j > 0 { print!(","); }
            print!("{}", grid[i][j]);
        }
        print!("]");
    }
    // r and c aren't really part of the problem; include placeholders 0,0
    println!("],\"r\":0,\"c\":0}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let (rows, cols, values) = build_grid(&mut rng, mode, t);
        let grid = generate_test_case(rows, cols, &values);
        print_json(&grid, 0, 0);
    }
}