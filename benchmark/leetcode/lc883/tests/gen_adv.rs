use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, flat: &Vec<i32>) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= n <= 50,
        flat.len() == n * n,
        forall|i: int| 0 <= i < flat.len() ==> 0 <= #[trigger] flat[i] <= 50,
    ensures
        1 <= grid.len() <= 50,
        grid.len() == n,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
        forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() ==> 0 <= #[trigger] grid[i][j] <= 50,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            1 <= n <= 50,
            flat.len() == n * n,
            forall|k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 50,
            grid.len() == i,
            i <= n,
            forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == n,
            forall|r: int, c: int| 0 <= r < grid.len() && 0 <= c < n ==> 0 <= #[trigger] grid[r][c] <= 50,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        assert(i < n);
        assert(i * n + n <= n * n) by (nonlinear_arith) requires i < n, n <= 50;

        while j < n
            invariant
                1 <= n <= 50,
                flat.len() == n * n,
                forall|k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 50,
                i < n,
                j <= n,
                row.len() == j,
                i * n + n <= n * n,
                forall|c: int| 0 <= c < row.len() ==> 0 <= #[trigger] row[c] <= 50,
            decreases n - j,
        {
            let base: usize = i * n;
            assert(base + j < n * n) by (nonlinear_arith)
                requires base == i * n, i < n, j < n, n <= 50;
            let idx: usize = base + j;
            let v: i32 = flat[idx];
            row.push(v);
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
        Self { state: if seed == 0 { 1 } else { seed } }
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_flat(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut flat: Vec<i32> = Vec::with_capacity(n * n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..(n * n) {
                flat.push(0);
            }
        }
        1 => {
            // all max (50)
            for _ in 0..(n * n) {
                flat.push(50);
            }
        }
        2 => {
            // random 0..=50
            for _ in 0..(n * n) {
                flat.push(rng.gen_range_i32(0, 50));
            }
        }
        3 => {
            // diagonal only
            for i in 0..n {
                for j in 0..n {
                    flat.push(if i == j { rng.gen_range_i32(1, 50) } else { 0 });
                }
            }
        }
        4 => {
            // sparse (mostly 0)
            for _ in 0..(n * n) {
                let r = rng.gen_range_usize(0, 9);
                if r == 0 {
                    flat.push(rng.gen_range_i32(1, 50));
                } else {
                    flat.push(0);
                }
            }
        }
        5 => {
            // single tall tower
            let pi = rng.gen_range_usize(0, n - 1);
            let pj = rng.gen_range_usize(0, n - 1);
            for i in 0..n {
                for j in 0..n {
                    flat.push(if i == pi && j == pj { 50 } else { 0 });
                }
            }
        }
        6 => {
            // one full row
            let r = rng.gen_range_usize(0, n - 1);
            for i in 0..n {
                for _ in 0..n {
                    flat.push(if i == r { rng.gen_range_i32(1, 50) } else { 0 });
                }
            }
        }
        7 => {
            // one full column
            let c = rng.gen_range_usize(0, n - 1);
            for _ in 0..n {
                for j in 0..n {
                    flat.push(if j == c { rng.gen_range_i32(1, 50) } else { 0 });
                }
            }
        }
        8 => {
            // binary 0/1
            for _ in 0..(n * n) {
                flat.push(rng.gen_range_i32(0, 1));
            }
        }
        9 => {
            // increasing values
            for i in 0..n {
                for j in 0..n {
                    let v = ((i + j) as i32) % 51;
                    flat.push(v);
                }
            }
        }
        _ => {
            for _ in 0..(n * n) {
                flat.push(rng.gen_range_i32(0, 50));
            }
        }
    }
    flat
}

fn print_json(grid: &Vec<Vec<i32>>) {
    print!("{{\"grid\":[");
    for (i, row) in grid.iter().enumerate() {
        if i > 0 {
            print!(",");
        }
        print!("[");
        for (j, v) in row.iter().enumerate() {
            if j > 0 {
                print!(",");
            }
            print!("{}", v);
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
        let n: usize = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 10,
            4 => 25,
            5 => 50,
            _ => rng.gen_range_usize(1, 50),
        };

        let flat = build_flat(&mut rng, n, mode);
        let grid = generate_test_case(n, &flat);
        print_json(&grid);
    }
}