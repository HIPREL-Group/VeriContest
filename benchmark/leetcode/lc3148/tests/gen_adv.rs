use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    values: &Vec<i32>,
) -> (grid: Vec<Vec<i32>>)
    requires
        2 <= m <= 1000,
        2 <= n <= 1000,
        4 <= (m * n) <= 100000,
        values.len() == m * n,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000,
    ensures
        grid.len() == m,
        2 <= grid.len() <= 1000,
        grid.len() > 0 ==> grid[0].len() == n,
        2 <= grid[0].len() <= 1000,
        4 <= grid.len() * grid[0].len() <= 100000,
        forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 1 <= #[trigger] grid[i][j] <= 100000,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            0 <= i <= m,
            grid.len() == i,
            2 <= m <= 1000,
            2 <= n <= 1000,
            4 <= m * n <= 100000,
            values.len() == m * n,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100000,
            forall |a: int| 0 <= a < i as int ==> #[trigger] grid[a].len() == n,
            forall |a: int, b: int| 0 <= a < i as int && 0 <= b < n as int ==> 1 <= #[trigger] grid[a][b] <= 100000,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        assert(i < m);
        assert(i * n + n <= m * n) by (nonlinear_arith)
            requires i < m, n >= 0, m >= 0;

        while j < n
            invariant
                0 <= j <= n,
                row.len() == j,
                2 <= n <= 1000,
                2 <= m <= 1000,
                i < m,
                values.len() == m * n,
                i * n + n <= m * n,
                forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100000,
                forall |b: int| 0 <= b < j as int ==> 1 <= #[trigger] row[b] <= 100000,
            decreases n - j,
        {
            let idx: usize = i * n + j;
            assert(idx < m * n) by (nonlinear_arith)
                requires i < m, j < n, idx == i * n + j;
            assert(idx < values.len());
            let v = values[idx];
            row.push(v);
            j = j + 1;
        }

        assert(row.len() == n);
        grid.push(row);
        i = i + 1;
    }

    assert(grid.len() == m);
    assert(grid[0].len() == n);
    assert(grid.len() * grid[0].len() == m * n);

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

fn pick_dims(rng: &mut Rng, mode: usize) -> (usize, usize) {
    match mode {
        0 => (2, 2),
        1 => (2, 3),
        2 => (3, 2),
        3 => (2, 1000),
        4 => (1000, 2),
        5 => (100, 1000),
        6 => {
            let m = rng.gen_range_usize(2, 10);
            let n = rng.gen_range_usize(2, 10);
            (m, n)
        }
        7 => {
            let m = rng.gen_range_usize(2, 50);
            let n = rng.gen_range_usize(2, 50);
            (m, n)
        }
        8 => (316, 316),
        9 => {
            // ensure m*n in range
            let m = rng.gen_range_usize(2, 100);
            let n = rng.gen_range_usize(2, 100);
            (m, n)
        }
        _ => {
            let m = rng.gen_range_usize(2, 20);
            let n = rng.gen_range_usize(2, 20);
            (m, n)
        }
    }
}

fn fill_values(rng: &mut Rng, mode: usize, m: usize, n: usize) -> Vec<i32> {
    let total = m * n;
    let mut v: Vec<i32> = Vec::with_capacity(total);
    match mode % 6 {
        0 => {
            // random
            for _ in 0..total {
                v.push(rng.gen_range_i32(1, 100000));
            }
        }
        1 => {
            // strictly increasing row-major
            let mut x: i32 = 1;
            for _ in 0..total {
                v.push(x);
                x += 1;
                if x > 100000 { x = 1; }
            }
        }
        2 => {
            // strictly decreasing
            let mut x: i32 = 100000;
            for _ in 0..total {
                v.push(x);
                x -= 1;
                if x < 1 { x = 100000; }
            }
        }
        3 => {
            // all same
            let c = rng.gen_range_i32(1, 100000);
            for _ in 0..total {
                v.push(c);
            }
        }
        4 => {
            // min and max only
            for _ in 0..total {
                if rng.next_u64() % 2 == 0 {
                    v.push(1);
                } else {
                    v.push(100000);
                }
            }
        }
        _ => {
            // mostly 1 with a spike
            for _ in 0..total {
                v.push(1);
            }
            let spikes = rng.gen_range_usize(1, 5.min(total));
            for _ in 0..spikes {
                let idx = rng.gen_range_usize(0, total - 1);
                v[idx] = rng.gen_range_i32(1, 100000);
            }
        }
    }
    v
}

fn print_json(grid: &[Vec<i32>]) {
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (mut m, mut n) = pick_dims(&mut rng, mode);
        // enforce constraints: 4 <= m*n <= 100000
        while m * n > 100000 {
            if m > n { m -= 1; } else { n -= 1; }
            if m < 2 { m = 2; }
            if n < 2 { n = 2; }
        }
        if m * n < 4 {
            m = 2; n = 2;
        }
        if m > 1000 { m = 1000; }
        if n > 1000 { n = 1000; }
        if m < 2 { m = 2; }
        if n < 2 { n = 2; }
        if m * n > 100000 {
            m = 2; n = 2;
        }

        let values = fill_values(&mut rng, t, m, n);
        let grid = generate_test_case(m, n, &values);
        print_json(&grid);
    }
}