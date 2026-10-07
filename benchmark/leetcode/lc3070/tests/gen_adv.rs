use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    k: i32,
    fill: i32,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= rows <= 1000,
        1 <= cols <= 1000,
        1 <= k <= 1_000_000_000,
        0 <= fill <= 1000,
    ensures
        ({
            let grid = result.0;
            let kk = result.1;
            &&& 1 <= grid.len() <= 1000
            &&& (forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len())
            &&& 1 <= grid[0].len() <= 1000
            &&& (forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 1000)
            &&& 1 <= kk <= 1_000_000_000
            &&& kk == k
        }),
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r <= rows,
            1 <= rows <= 1000,
            1 <= cols <= 1000,
            0 <= fill <= 1000,
            grid.len() == r,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 0 <= #[trigger] grid[i][j] <= 1000,
        decreases rows - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= c <= cols,
                1 <= cols <= 1000,
                0 <= fill <= 1000,
                row.len() == c,
                forall |j: int| 0 <= j < row.len() ==> 0 <= #[trigger] row[j] <= 1000,
            decreases cols - c,
        {
            row.push(fill);
            c = c + 1;
        }
        assert(row.len() == cols);
        grid.push(row);
        r = r + 1;
    }

    assert(grid.len() == rows);
    assert(grid[0].len() == cols);

    (grid, k)
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn print_case(grid: &Vec<Vec<i32>>, k: i32) {
    print!("{{\"grid\":[");
    for (i, row) in grid.iter().enumerate() {
        if i > 0 { print!(","); }
        print!("[");
        for (j, v) in row.iter().enumerate() {
            if j > 0 { print!(","); }
            print!("{}", v);
        }
        print!("]");
    }
    println!("],\"k\":{}}}", k);
}

fn pick_params(rng: &mut Rng, mode: usize) -> (usize, usize, i32, i32) {
    match mode {
        0 => (1, 1, 1, 0),
        1 => (1, 1, 1_000_000_000, 1000),
        2 => (1000, 1, rng.gen_i32(1, 1_000_000_000), rng.gen_i32(0, 1000)),
        3 => (1, 1000, rng.gen_i32(1, 1_000_000_000), rng.gen_i32(0, 1000)),
        4 => (1000, 1000, 1, 0),
        5 => (1000, 1000, 1_000_000_000, 1000),
        6 => {
            let r = rng.gen_usize(1, 50);
            let c = rng.gen_usize(1, 50);
            (r, c, rng.gen_i32(1, 1000), rng.gen_i32(0, 1000))
        }
        7 => {
            let r = rng.gen_usize(1, 100);
            let c = rng.gen_usize(1, 100);
            (r, c, 1, rng.gen_i32(0, 1000))
        }
        8 => {
            let r = rng.gen_usize(1, 100);
            let c = rng.gen_usize(1, 100);
            (r, c, 1_000_000_000, 0)
        }
        9 => {
            let r = rng.gen_usize(1, 30);
            let c = rng.gen_usize(1, 30);
            (r, c, rng.gen_i32(1, 100), rng.gen_i32(0, 10))
        }
        _ => {
            let r = rng.gen_usize(1, 200);
            let c = rng.gen_usize(1, 200);
            (r, c, rng.gen_i32(1, 1_000_000_000), rng.gen_i32(0, 1000))
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (rows, cols, k, fill) = pick_params(&mut rng, mode);
        let (grid, kk) = generate_test_case(rows, cols, k, fill);
        print_case(&grid, kk);
    }
}