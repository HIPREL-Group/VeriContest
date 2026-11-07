use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    filler: i32,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= m <= 50,
        1 <= n <= 50,
        0 <= filler < 2500,
    ensures
        1 <= grid.len() <= 50,
        1 <= grid[0].len() <= 50,
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int|
            0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] < 2500,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            1 <= m <= 50,
            1 <= n <= 50,
            0 <= filler < 2500,
            0 <= i <= m,
            grid.len() == i,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == n as int,
            forall |r: int, c: int|
                0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] < 2500,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 50,
                0 <= filler < 2500,
                0 <= j <= n,
                row.len() == j,
                forall |c: int| 0 <= c < row.len() ==> 0 <= #[trigger] row[c] < 2500,
            decreases n - j,
        {
            row.push(filler);
            j = j + 1;
        }
        grid.push(row);
        i = i + 1;
    }
    grid
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn clamp_val(v: i32) -> i32 {
    if v < 0 { 0 } else if v >= 2500 { 2499 } else { v }
}

fn build_grid(m: usize, n: usize, vals: &[i32]) -> Vec<Vec<i32>> {
    // Build via generator with filler=0 then overwrite
    let mut grid = generate_test_case(m, n, 0);
    let mut k = 0;
    for i in 0..m {
        for j in 0..n {
            if k < vals.len() {
                grid[i][j] = clamp_val(vals[k]);
            }
            k += 1;
        }
    }
    grid
}

fn print_grid(grid: &Vec<Vec<i32>>) {
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
    println!("]}}");
}

fn verified_only_print(grid: Vec<Vec<i32>>) {
    // verify constraints exec-side then print
    print_grid(&grid);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n) = match mode {
            0 => (1usize, 1usize),
            1 => (1, rng.gen_range_usize(1, 50)),
            2 => (rng.gen_range_usize(1, 50), 1),
            3 => (50, 50),
            4 => (50, rng.gen_range_usize(1, 50)),
            5 => (rng.gen_range_usize(1, 50), 50),
            _ => (rng.gen_range_usize(1, 50), rng.gen_range_usize(1, 50)),
        };

        let size = m * n;
        let mut vals: Vec<i32> = Vec::with_capacity(size);

        match mode {
            0 => {
                // single cell random
                for _ in 0..size {
                    vals.push(rng.gen_range_i32(0, 2499));
                }
            }
            1 | 2 => {
                // small row/col, random
                for _ in 0..size {
                    vals.push(rng.gen_range_i32(0, 2499));
                }
            }
            3 => {
                // max size all same value (forces worst-case ops)
                let v = rng.gen_range_i32(0, 2499);
                for _ in 0..size {
                    vals.push(v);
                }
            }
            4 => {
                // decreasing columns - worst case
                for i in 0..m {
                    for _ in 0..n {
                        let v = if 2499 >= i as i32 { 2499 - i as i32 } else { 0 };
                        vals.push(clamp_val(v));
                    }
                }
            }
            5 => {
                // already strictly increasing columns
                for i in 0..m {
                    for _ in 0..n {
                        let v = if i < 2500 { i as i32 } else { 2499 };
                        vals.push(clamp_val(v));
                    }
                }
            }
            6 => {
                // all zeros
                for _ in 0..size { vals.push(0); }
            }
            7 => {
                // all max
                for _ in 0..size { vals.push(2499); }
            }
            8 => {
                // alternating high/low
                for i in 0..m {
                    for _ in 0..n {
                        vals.push(if i % 2 == 0 { 2499 } else { 0 });
                    }
                }
            }
            _ => {
                // fully random
                for _ in 0..size {
                    vals.push(rng.gen_range_i32(0, 2499));
                }
            }
        }

        let grid = build_grid(m, n, &vals);
        verified_only_print(grid);
    }
}