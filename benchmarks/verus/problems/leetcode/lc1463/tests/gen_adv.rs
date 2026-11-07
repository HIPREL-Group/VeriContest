use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    values: &Vec<i32>,
) -> (grid: Vec<Vec<i32>>)
    requires
        2 <= rows <= 70,
        2 <= cols <= 70,
        values.len() == rows * cols,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100,
    ensures
        2 <= grid.len() <= 70,
        2 <= grid[0].len() <= 70,
        grid.len() == rows,
        grid[0].len() == cols,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall|i: int, j: int|
            0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 0 <= #[trigger] grid[i][j] <= 100,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < rows
        invariant
            2 <= rows <= 70,
            2 <= cols <= 70,
            values.len() == rows * cols,
            0 <= i <= rows,
            grid.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 100,
            forall|k: int| 0 <= k < i ==> #[trigger] grid[k].len() == cols,
            forall|k: int, c: int|
                0 <= k < i && 0 <= c < cols ==> 0 <= #[trigger] grid[k][c] <= 100,
        decreases rows - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        while j < cols
            invariant
                2 <= rows <= 70,
                2 <= cols <= 70,
                values.len() == rows * cols,
                0 <= i < rows,
                0 <= j <= cols,
                row.len() == j,
                forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 100,
                forall|c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 100,
            decreases cols - j,
        {
            // Prove i * cols + j doesn't overflow
            assert(i < rows);
            assert(j < cols);
            assert(rows <= 70);
            assert(cols <= 70);
            assert(i * cols <= (rows - 1) * cols) by (nonlinear_arith)
                requires i < rows, cols >= 0, i >= 0;
            assert((rows - 1) * cols <= 69 * 70) by (nonlinear_arith)
                requires rows <= 70, cols <= 70, rows >= 2, cols >= 2;
            let idx: usize = i * cols + j;
            assert(idx < rows * cols) by (nonlinear_arith)
                requires i < rows, j < cols, i >= 0, j >= 0, cols >= 0,
                         idx == i * cols + j;
            assert(idx < values.len());
            let v = values[idx];
            assert(0 <= v <= 100);
            row.push(v);
            j = j + 1;
        }

        assert(row.len() == cols);
        grid.push(row);
        i = i + 1;
    }

    assert(grid.len() == rows);
    assert(grid[0].len() == cols);

    grid
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_values(rng: &mut Rng, rows: usize, cols: usize, mode: usize) -> Vec<i32> {
    let n = rows * cols;
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
        }
        1 => {
            for _ in 0..n {
                v.push(0);
            }
        }
        2 => {
            for _ in 0..n {
                v.push(100);
            }
        }
        3 => {
            for _ in 0..n {
                v.push(1);
            }
        }
        4 => {
            // sparse
            for _ in 0..n {
                if rng.next_u64() % 10 == 0 {
                    v.push(rng.gen_range_i32(1, 100));
                } else {
                    v.push(0);
                }
            }
        }
        5 => {
            // a single big cell
            for _ in 0..n {
                v.push(0);
            }
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = 100;
        }
        6 => {
            // diagonal heavy
            for i in 0..rows {
                for j in 0..cols {
                    if i == j || i + j == cols - 1 {
                        v.push(100);
                    } else {
                        v.push(0);
                    }
                }
            }
        }
        7 => {
            // only bottom row has cherries
            for i in 0..rows {
                for _ in 0..cols {
                    if i == rows - 1 {
                        v.push(rng.gen_range_i32(0, 100));
                    } else {
                        v.push(0);
                    }
                }
            }
        }
        8 => {
            // only top row
            for i in 0..rows {
                for _ in 0..cols {
                    if i == 0 {
                        v.push(rng.gen_range_i32(0, 100));
                    } else {
                        v.push(0);
                    }
                }
            }
        }
        9 => {
            // stripes
            for i in 0..rows {
                for _ in 0..cols {
                    if i % 2 == 0 {
                        v.push(rng.gen_range_i32(0, 100));
                    } else {
                        v.push(0);
                    }
                }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
        }
    }
    v
}

fn print_json(grid: &Vec<Vec<i32>>) {
    print!("{{\"grid\":[");
    for i in 0..grid.len() {
        if i > 0 {
            print!(",");
        }
        print!("[");
        for j in 0..grid[i].len() {
            if j > 0 {
                print!(",");
            }
            print!("{}", grid[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let rows: usize = match t % 7 {
            0 => 2,
            1 => 3,
            2 => 4,
            3 => 10,
            4 => 70,
            5 => rng.gen_range_usize(2, 70),
            _ => rng.gen_range_usize(2, 20),
        };
        let cols: usize = match (t / 7) % 7 {
            0 => 2,
            1 => 3,
            2 => 7,
            3 => 70,
            4 => 5,
            5 => rng.gen_range_usize(2, 70),
            _ => rng.gen_range_usize(2, 20),
        };

        let values = make_values(&mut rng, rows, cols, mode);
        let grid = generate_test_case(rows, cols, &values);
        print_json(&grid);
    }
}