use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    cols: &Vec<i32>,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= m <= 10,
        1 <= n <= 10,
        cols.len() == n,
        forall |j: int| 0 <= j < cols.len() ==> 0 <= #[trigger] cols[j] <= 9,
    ensures
        1 <= grid.len() <= 10,
        forall |i: int| 0 <= i < grid.len() ==> 1 <= #[trigger] grid[i].len() <= 10,
        forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 9,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            1 <= m <= 10,
            1 <= n <= 10,
            cols.len() == n,
            i <= m,
            grid.len() == i,
            forall |k: int| 0 <= k < cols.len() ==> 0 <= #[trigger] cols[k] <= 9,
            forall |k: int| 0 <= k < grid.len() ==> #[trigger] grid[k].len() == n as int,
            forall |k: int, jj: int| 0 <= k < grid.len() && 0 <= jj < n as int ==> 0 <= #[trigger] grid[k][jj] <= 9,
            forall |k: int, jj: int| 0 <= k < grid.len() && 0 <= jj < n as int ==> #[trigger] grid[k][jj] == cols[jj],
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 10,
                cols.len() == n,
                j <= n,
                row.len() == j,
                forall |k: int| 0 <= k < cols.len() ==> 0 <= #[trigger] cols[k] <= 9,
                forall |jj: int| 0 <= jj < j as int ==> #[trigger] row[jj] == cols[jj],
                forall |jj: int| 0 <= jj < j as int ==> 0 <= #[trigger] row[jj] <= 9,
            decreases n - j,
        {
            row.push(cols[j]);
            j = j + 1;
        }
        assert(row.len() == n as int);
        grid.push(row);
        i = i + 1;
    }
    assert(grid.len() == m as int);
    assert(grid[0].len() == n as int);
    grid
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: if seed == 0 { 1 } else { seed } }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
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

fn gen_case(rng: &mut Rng, mode: usize) -> (usize, usize, Vec<i32>) {
    let m = rng.gen_range(1, 10);
    let n = rng.gen_range(1, 10);
    let mut cols: Vec<i32> = Vec::new();
    match mode {
        0 => {
            // all same value -> fails column-diff when n>1
            let v = rng.gen_range(0, 9) as i32;
            for _ in 0..n { cols.push(v); }
        }
        1 => {
            // alternating 0/1
            for j in 0..n { cols.push((j % 2) as i32); }
        }
        2 => {
            // strictly distinct if n<=10
            for j in 0..n { cols.push(j as i32); }
        }
        3 => {
            // adjacent duplicate somewhere
            for j in 0..n { cols.push((j / 2) as i32); }
        }
        4 => {
            // all zeros
            for _ in 0..n { cols.push(0); }
        }
        5 => {
            // all nines
            for _ in 0..n { cols.push(9); }
        }
        6 => {
            // random
            for _ in 0..n { cols.push(rng.gen_range(0, 9) as i32); }
        }
        7 => {
            // two distinct alternation
            let a = rng.gen_range(0, 9) as i32;
            let mut b = rng.gen_range(0, 9) as i32;
            if b == a { b = (a + 1) % 10; }
            for j in 0..n {
                cols.push(if j % 2 == 0 { a } else { b });
            }
        }
        8 => {
            // decreasing
            for j in 0..n { cols.push(((n - 1 - j) % 10) as i32); }
        }
        _ => {
            for _ in 0..n { cols.push(rng.gen_range(0, 9) as i32); }
        }
    }
    (m, n, cols)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 10;
    let total = 200;
    for t in 0..total {
        let mode = t % modes;
        let (m, n, cols) = gen_case(&mut rng, mode);
        let grid = generate_test_case(m, n, &cols);
        print_grid(&grid);
    }
}