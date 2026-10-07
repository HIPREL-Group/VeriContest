use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    values: &Vec<i32>,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= m <= 15,
        1 <= n <= 15,
        values.len() == m * n,
        forall|k: int| 0 <= k < values.len() ==> -4 <= #[trigger] values[k] <= 4,
    ensures
        1 <= grid.len() <= 15,
        grid.len() == m,
        grid[0].len() == n,
        1 <= grid[0].len() <= 15,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall|i: int, j: int|
            0 <= i < grid.len() && 0 <= j < grid[i].len()
                ==> -4 <= #[trigger] grid[i][j] <= 4,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            1 <= m <= 15,
            1 <= n <= 15,
            values.len() == m * n,
            forall|k: int| 0 <= k < values.len() ==> -4 <= #[trigger] values[k] <= 4,
            0 <= i <= m,
            grid.len() == i,
            forall|a: int| 0 <= a < grid.len() ==> #[trigger] grid[a].len() == n,
            forall|a: int, b: int|
                0 <= a < grid.len() && 0 <= b < n
                    ==> -4 <= #[trigger] grid[a][b] <= 4,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        proof {
            assert(i < m);
            assert(i + 1 <= m);
            assert((i + 1) * n <= m * n) by (nonlinear_arith)
                requires i + 1 <= m, n >= 0;
            assert(i * n + n == (i + 1) * n) by (nonlinear_arith);
            assert(i * n + n <= m * n);
            assert(i * n <= m * n) by (nonlinear_arith)
                requires i <= m, n >= 0;
        }

        let base: usize = i * n;

        while j < n
            invariant
                1 <= m <= 15,
                1 <= n <= 15,
                values.len() == m * n,
                forall|k: int| 0 <= k < values.len() ==> -4 <= #[trigger] values[k] <= 4,
                0 <= i < m,
                base == i * n,
                base + n <= values.len(),
                0 <= j <= n,
                row.len() == j,
                forall|b: int| 0 <= b < row.len() ==> -4 <= #[trigger] row[b] <= 4,
            decreases n - j,
        {
            let idx = base + j;
            row.push(values[idx]);
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

fn make_values(rng: &mut Rng, m: usize, n: usize, mode: usize) -> Vec<i32> {
    let size = m * n;
    let mut v: Vec<i32> = Vec::with_capacity(size);
    for idx in 0..size {
        let x: i32 = match mode {
            0 => rng.gen_range_i32(-4, 4),
            1 => -rng.gen_range_i32(1, 4), // all negative
            2 => rng.gen_range_i32(1, 4),  // all positive
            3 => {
                // many zeros
                if rng.next_u64() % 3 == 0 { 0 } else { rng.gen_range_i32(-4, 4) }
            }
            4 => {
                // mostly 1s and -1s
                let c = rng.next_u64() % 4;
                match c {
                    0 => 1,
                    1 => -1,
                    2 => 0,
                    _ => rng.gen_range_i32(-4, 4),
                }
            }
            5 => {
                // extremes only
                if rng.next_u64() % 2 == 0 { 4 } else { -4 }
            }
            6 => {
                // zero row/col test: place zero at first cell
                if idx == 0 { 0 } else { rng.gen_range_i32(-4, 4) }
            }
            7 => {
                // zero at final cell
                if idx == size - 1 { 0 } else { rng.gen_range_i32(-4, 4) }
            }
            8 => {
                // alternating sign
                if idx % 2 == 0 { rng.gen_range_i32(1, 4) } else { -rng.gen_range_i32(1, 4) }
            }
            9 => {
                // mostly negative with sporadic positives
                if rng.next_u64() % 5 == 0 { rng.gen_range_i32(1, 4) } else { -rng.gen_range_i32(1, 4) }
            }
            _ => rng.gen_range_i32(-4, 4),
        };
        v.push(x);
    }
    v
}

fn print_json(grid: &Vec<Vec<i32>>) {
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n): (usize, usize) = match t % 13 {
            0 => (1, 1),
            1 => (1, 15),
            2 => (15, 1),
            3 => (15, 15),
            4 => (2, 2),
            5 => (3, 3),
            6 => (4, 5),
            7 => (5, 4),
            8 => (15, 15),
            9 => (10, 10),
            10 => (7, 8),
            11 => (1, 2),
            _ => {
                let mm = rng.gen_range_usize(1, 15);
                let nn = rng.gen_range_usize(1, 15);
                (mm, nn)
            }
        };

        let values = make_values(&mut rng, m, n, mode);
        let grid = generate_test_case(m, n, &values);
        print_json(&grid);
    }
}