use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    fill: i32,
) -> (grid: Vec<Vec<i32>>)
    requires
        3 <= m <= 150,
        3 <= n <= 150,
        0 <= fill <= 1_000_000,
    ensures
        3 <= grid.len() <= 150,
        forall |i: int| 0 <= i < grid.len() ==> 3 <= #[trigger] grid[i].len() <= 150,
        forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 1_000_000,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            3 <= m <= 150,
            3 <= n <= 150,
            0 <= fill <= 1_000_000,
            i <= m,
            grid.len() == i,
            forall |k: int| 0 <= k < grid.len() ==> #[trigger] grid[k].len() == n,
            forall |k: int, l: int| 0 <= k < grid.len() && 0 <= l < grid[k].len() ==> 0 <= #[trigger] grid[k][l] <= 1_000_000,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                3 <= n <= 150,
                0 <= fill <= 1_000_000,
                j <= n,
                row.len() == j,
                forall |l: int| 0 <= l < row.len() ==> 0 <= #[trigger] row[l] <= 1_000_000,
            decreases n - j,
        {
            row.push(fill);
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
        Self { state: seed.wrapping_add(1) }
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let (m, n, fill) = match mode {
            0 => (3usize, 3usize, 0i32),
            1 => (3, 3, 1_000_000),
            2 => (150, 150, 1_000_000),
            3 => (150, 150, 0),
            4 => (3, 150, rng.gen_range_i32(0, 1_000_000)),
            5 => (150, 3, rng.gen_range_i32(0, 1_000_000)),
            6 => (rng.gen_range_usize(3, 10), rng.gen_range_usize(3, 10), rng.gen_range_i32(0, 1_000_000)),
            7 => (rng.gen_range_usize(3, 150), rng.gen_range_usize(3, 150), 500_000),
            8 => (rng.gen_range_usize(3, 50), rng.gen_range_usize(3, 50), rng.gen_range_i32(0, 100)),
            _ => (rng.gen_range_usize(3, 150), rng.gen_range_usize(3, 150), rng.gen_range_i32(0, 1_000_000)),
        };
        let grid = generate_test_case(m, n, fill);
        print_grid(&grid);
    }
}