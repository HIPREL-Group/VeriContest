use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    threshold: i32,
    values: &Vec<Vec<i32>>,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        3 <= rows <= 500,
        3 <= cols <= 500,
        0 <= threshold <= 255,
        values.len() == rows,
        forall |r: int| 0 <= r < values.len() ==> #[trigger] values[r].len() == cols,
        forall |r: int, c: int| 0 <= r < values.len() && 0 <= c < values[r].len() ==> 0 <= #[trigger] values[r][c] <= 255,
    ensures
        3 <= result.0.len() <= 500,
        forall |r: int| 0 <= r < result.0.len() ==> #[trigger] result.0[r].len() == result.0[0].len(),
        3 <= result.0[0].len() <= 500,
        forall |r: int, c: int| 0 <= r < result.0.len() && 0 <= c < result.0[r].len() ==> 0 <= #[trigger] result.0[r][c] <= 255,
        0 <= result.1 <= 255,
{
    let mut image: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            3 <= rows <= 500,
            3 <= cols <= 500,
            values.len() == rows,
            forall |i: int| 0 <= i < values.len() ==> #[trigger] values[i].len() == cols,
            forall |i: int, c: int| 0 <= i < values.len() && 0 <= c < values[i].len() ==> 0 <= #[trigger] values[i][c] <= 255,
            0 <= r <= rows,
            image.len() == r,
            forall |i: int| 0 <= i < image.len() ==> #[trigger] image[i].len() == cols,
            forall |i: int, c: int| 0 <= i < image.len() && 0 <= c < image[i].len() ==> 0 <= #[trigger] image[i][c] <= 255,
        decreases rows - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                3 <= cols <= 500,
                r < rows,
                values.len() == rows,
                values[r as int].len() == cols,
                forall |cc: int| 0 <= cc < values[r as int].len() ==> 0 <= #[trigger] values[r as int][cc] <= 255,
                0 <= c <= cols,
                row.len() == c,
                forall |cc: int| 0 <= cc < row.len() ==> 0 <= #[trigger] row[cc] <= 255,
            decreases cols - c,
        {
            let v = values[r][c];
            row.push(v);
            c = c + 1;
        }
        image.push(row);
        r = r + 1;
    }

    assert(image.len() == rows);
    assert(image[0].len() == cols);

    (image, threshold)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_mul(2862933555777941757).wrapping_add(3037000493) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn build_grid(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize, i32, Vec<Vec<i32>>) {
    let (rows, cols): (usize, usize) = match mode {
        0 => (3, 3),
        1 => (3, rng.gen_range_usize(3, 10)),
        2 => (rng.gen_range_usize(3, 10), 3),
        3 => (500, 500),
        4 => (rng.gen_range_usize(3, 20), rng.gen_range_usize(3, 20)),
        5 => (5, 5),
        6 => (4, 7),
        7 => (rng.gen_range_usize(3, 50), rng.gen_range_usize(3, 50)),
        8 => (3, 500),
        9 => (500, 3),
        _ => (rng.gen_range_usize(3, 30), rng.gen_range_usize(3, 30)),
    };

    let threshold: i32 = match mode {
        0 => 0,
        1 => 255,
        2 => rng.gen_range_i32(0, 255),
        3 => rng.gen_range_i32(0, 10),
        4 => rng.gen_range_i32(0, 255),
        5 => 3,
        6 => 12,
        7 => rng.gen_range_i32(0, 50),
        8 => rng.gen_range_i32(0, 255),
        9 => rng.gen_range_i32(0, 255),
        _ => rng.gen_range_i32(0, 255),
    };

    let mut grid: Vec<Vec<i32>> = Vec::with_capacity(rows);
    match mode {
        0 => {
            // all same
            let v = rng.gen_range_i32(0, 255);
            for _ in 0..rows {
                let mut row = Vec::with_capacity(cols);
                for _ in 0..cols { row.push(v); }
                grid.push(row);
            }
        }
        1 => {
            // gradient
            for i in 0..rows {
                let mut row = Vec::with_capacity(cols);
                for j in 0..cols {
                    let v = ((i + j) as i32) % 256;
                    row.push(v);
                }
                grid.push(row);
            }
        }
        2 => {
            // random small range
            for _ in 0..rows {
                let mut row = Vec::with_capacity(cols);
                for _ in 0..cols { row.push(rng.gen_range_i32(0, 10)); }
                grid.push(row);
            }
        }
        3 => {
            // large grid, random
            for _ in 0..rows {
                let mut row = Vec::with_capacity(cols);
                for _ in 0..cols { row.push(rng.gen_range_i32(0, 255)); }
                grid.push(row);
            }
        }
        4 => {
            // alternating
            for i in 0..rows {
                let mut row = Vec::with_capacity(cols);
                for j in 0..cols {
                    row.push(if (i + j) % 2 == 0 { 0 } else { 255 });
                }
                grid.push(row);
            }
        }
        5 => {
            // example 1 like
            for i in 0..rows {
                let mut row = Vec::with_capacity(cols);
                for j in 0..cols {
                    row.push(((5 + i * 3 + j) as i32).min(255));
                }
                grid.push(row);
            }
        }
        6 => {
            for i in 0..rows {
                let mut row = Vec::with_capacity(cols);
                for j in 0..cols {
                    row.push(((10 + i * 5 + j * 10) as i32).min(255));
                }
                grid.push(row);
            }
        }
        7 => {
            // clusters
            for i in 0..rows {
                let mut row = Vec::with_capacity(cols);
                for j in 0..cols {
                    let base = if (i / 3 + j / 3) % 2 == 0 { 50 } else { 200 };
                    let jitter = rng.gen_range_i32(0, 3);
                    row.push((base + jitter).min(255));
                }
                grid.push(row);
            }
        }
        8 | 9 => {
            for _ in 0..rows {
                let mut row = Vec::with_capacity(cols);
                for _ in 0..cols { row.push(rng.gen_range_i32(0, 255)); }
                grid.push(row);
            }
        }
        _ => {
            let _ = t;
            for _ in 0..rows {
                let mut row = Vec::with_capacity(cols);
                for _ in 0..cols { row.push(rng.gen_range_i32(0, 255)); }
                grid.push(row);
            }
        }
    }

    (rows, cols, threshold, grid)
}

fn print_json(grid: &Vec<Vec<i32>>, threshold: i32) {
    print!("{{\"image\":[");
    for i in 0..grid.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..grid[i].len() {
            if j > 0 { print!(","); }
            print!("{}", grid[i][j]);
        }
        print!("]");
    }
    println!("],\"threshold\":{}}}", threshold);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 { args[1].parse().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (rows, cols, threshold, grid) = build_grid(&mut rng, mode, t);
        let (out_grid, out_th) = generate_test_case(rows, cols, threshold, &grid);
        print_json(&out_grid, out_th);
    }
}