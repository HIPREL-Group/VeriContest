use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    values: &Vec<i32>,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= n <= 50,
        values.len() == n * n,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 50,
    ensures
        grid.len() == n,
        1 <= grid.len() <= 50,
        forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
        forall |i: int, j: int|
            0 <= i < grid.len() && 0 <= j < grid.len() ==> 0 <= #[trigger] grid[i][j] <= 50,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            1 <= n <= 50,
            values.len() == n * n,
            0 <= i <= n,
            grid.len() == i,
            forall |a: int| 0 <= a < values.len() ==> 0 <= #[trigger] values[a] <= 50,
            forall |a: int| 0 <= a < i as int ==> #[trigger] grid[a].len() == n,
            forall |a: int, b: int|
                0 <= a < i as int && 0 <= b < n as int ==> 0 <= #[trigger] grid[a][b] <= 50,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 50,
                values.len() == n * n,
                0 <= i < n,
                0 <= j <= n,
                row.len() == j,
                forall |a: int| 0 <= a < values.len() ==> 0 <= #[trigger] values[a] <= 50,
                forall |b: int| 0 <= b < j as int ==> 0 <= #[trigger] row[b] <= 50,
            decreases n - j,
        {
            // i < n <= 50, j < n <= 50, so i*n + j < n*n = values.len() <= 2500, fits in usize
            assert(i < n);
            assert(j < n);
            assert(i * n <= (n - 1) * n) by (nonlinear_arith) requires i < n, n <= 50;
            assert(i * n + j < n * n) by (nonlinear_arith) requires i < n, j < n, n <= 50;
            let idx: usize = i * n + j;
            assert(idx < values.len());
            let v = values[idx];
            row.push(v);
            j = j + 1;
        }
        assert(row.len() == n);
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
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_values(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let total = n * n;
    let mut v: Vec<i32> = Vec::with_capacity(total);
    match mode {
        0 => {
            // all zeros
            for _ in 0..total { v.push(0); }
        }
        1 => {
            // all ones
            for _ in 0..total { v.push(1); }
        }
        2 => {
            // all max (50)
            for _ in 0..total { v.push(50); }
        }
        3 => {
            // checkerboard 0/50
            for i in 0..n {
                for j in 0..n {
                    v.push(if (i + j) % 2 == 0 { 0 } else { 50 });
                }
            }
        }
        4 => {
            // random small 0..3
            for _ in 0..total { v.push(rng.gen_range_i32(0, 3)); }
        }
        5 => {
            // random 0..50 uniform
            for _ in 0..total { v.push(rng.gen_range_i32(0, 50)); }
        }
        6 => {
            // one tall tower in center
            for _ in 0..total { v.push(0); }
            let c = n / 2;
            let idx = c * n + c;
            v[idx] = 50;
        }
        7 => {
            // border = 50, interior = 0
            for i in 0..n {
                for j in 0..n {
                    if i == 0 || j == 0 || i == n - 1 || j == n - 1 {
                        v.push(50);
                    } else {
                        v.push(0);
                    }
                }
            }
        }
        8 => {
            // interior = 50, border = 0 (adjacency glue maximal)
            for i in 0..n {
                for j in 0..n {
                    if i == 0 || j == 0 || i == n - 1 || j == n - 1 {
                        v.push(0);
                    } else {
                        v.push(50);
                    }
                }
            }
        }
        9 => {
            // stripes
            for i in 0..n {
                for _ in 0..n {
                    v.push(if i % 2 == 0 { 0 } else { rng.gen_range_i32(1, 50) });
                }
            }
        }
        _ => {
            // random with many zeros
            for _ in 0..total {
                if rng.next_u64() % 3 == 0 {
                    v.push(rng.gen_range_i32(1, 50));
                } else {
                    v.push(0);
                }
            }
        }
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => 1 + (t % 5),
            1 => 2 + (t % 10),
            2 => 50,
            3 => if t % 2 == 0 { 2 } else { 10 },
            4 => 5 + (t % 8),
            5 => rng.gen_range_usize(1, 50),
            6 => 50,
            7 => 3 + (t % 20),
            8 => 4 + (t % 15),
            9 => 1 + (t % 50),
            _ => rng.gen_range_usize(1, 50),
        };
        let n = if n < 1 { 1 } else if n > 50 { 50 } else { n };

        let values = make_values(&mut rng, n, mode);
        let grid = generate_test_case(n, &values);
        print_json(&grid);
    }
}