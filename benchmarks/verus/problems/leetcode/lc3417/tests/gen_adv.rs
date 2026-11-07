use vstd::prelude::*;

verus! {

pub fn generate_test_case(m: usize, n: usize, values: &Vec<Vec<i32>>) -> (grid: Vec<Vec<i32>>)
    requires
        2 <= m <= 50,
        2 <= n <= 50,
        values.len() == m,
        forall |i: int| 0 <= i < values.len() ==> #[trigger] values[i].len() == n,
        forall |i: int, j: int| 0 <= i < values.len() && 0 <= j < values[i].len() ==>
            1 <= #[trigger] values[i][j] <= 2500,
    ensures
        2 <= grid.len() <= 50,
        2 <= grid[0].len() <= 50,
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int|
            0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 2500,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            2 <= m <= 50,
            2 <= n <= 50,
            values.len() == m,
            forall |k: int| 0 <= k < values.len() ==> #[trigger] values[k].len() == n,
            forall |k: int, j: int| 0 <= k < values.len() && 0 <= j < values[k].len() ==>
                1 <= #[trigger] values[k][j] <= 2500,
            0 <= i <= m,
            grid.len() == i,
            forall |k: int| 0 <= k < grid.len() ==> #[trigger] grid[k].len() == n,
            forall |k: int, j: int| 0 <= k < grid.len() && 0 <= j < grid[k].len() ==>
                1 <= #[trigger] grid[k][j] <= 2500,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let src = &values[i];
        let mut j: usize = 0;
        while j < n
            invariant
                2 <= n <= 50,
                i < m,
                values.len() == m,
                src == &values[i as int],
                src.len() == n,
                forall |k: int| 0 <= k < src.len() ==> 1 <= #[trigger] src[k] <= 2500,
                0 <= j <= n,
                row.len() == j,
                forall |k: int| 0 <= k < row.len() ==> #[trigger] row[k] == src[k],
                forall |k: int| 0 <= k < row.len() ==> 1 <= #[trigger] row[k] <= 2500,
            decreases n - j,
        {
            row.push(src[j]);
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
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
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
        let v = (self.next_u64() % span) as i32;
        lo + v
    }
}

fn make_values(rng: &mut Rng, mode: usize, m: usize, n: usize) -> Vec<Vec<i32>> {
    let mut v: Vec<Vec<i32>> = Vec::with_capacity(m);
    for i in 0..m {
        let mut row: Vec<i32> = Vec::with_capacity(n);
        for j in 0..n {
            let val: i32 = match mode {
                0 => rng.gen_range_i32(1, 2500),
                1 => 1,
                2 => 2500,
                3 => {
                    let x = ((i * n + j) as i32) % 2500 + 1;
                    x
                }
                4 => {
                    if (i + j) % 2 == 0 { 1 } else { 2500 }
                }
                5 => rng.gen_range_i32(1, 10),
                6 => {
                    let x = (i as i32 + 1) * (j as i32 + 1);
                    let x2 = x % 2500 + 1;
                    if x2 < 1 { 1 } else if x2 > 2500 { 2500 } else { x2 }
                }
                7 => {
                    let base = ((i % n) + 1) as i32;
                    let x = (base % 2500) + 1;
                    if x > 2500 { 2500 } else { x }
                }
                8 => {
                    if i == 0 && j == 0 { 1 } else if i + 1 == m && j + 1 == n { 2500 } else { rng.gen_range_i32(1, 2500) }
                }
                9 => rng.gen_range_i32(1, 100),
                _ => rng.gen_range_i32(1, 2500),
            };
            let val = if val < 1 { 1 } else if val > 2500 { 2500 } else { val };
            row.push(val);
        }
        v.push(row);
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
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n) = match mode {
            0 => (2usize, 2usize),
            1 => (50usize, 50usize),
            2 => (2usize, 50usize),
            3 => (50usize, 2usize),
            4 => (3usize, 3usize),
            5 => (rng.gen_range_usize(2, 10), rng.gen_range_usize(2, 10)),
            6 => (rng.gen_range_usize(2, 50), rng.gen_range_usize(2, 50)),
            7 => (5usize, 7usize),
            8 => (10usize, 10usize),
            _ => (rng.gen_range_usize(2, 20), rng.gen_range_usize(2, 20)),
        };

        let values = make_values(&mut rng, mode, m, n);
        let grid = generate_test_case(m, n, &values);
        print_json(&grid);
    }
}