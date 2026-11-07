use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<Vec<i32>>) -> (grid: Vec<Vec<i32>>)
    ensures
        1 <= grid.len() <= 100,
        forall|r: int| 0 <= r < grid.len() ==> 1 <= #[trigger] grid[r].len() <= 100,
        forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall|r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> -100 <= #[trigger] grid[r][c] <= 100,
        forall|r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() - 1 ==> #[trigger] grid[r][c] >= grid[r][c + 1],
        forall|r: int, c: int| 0 <= r < grid.len() - 1 && 0 <= c < grid[r].len() ==> #[trigger] grid[r][c] >= grid[r + 1][c],
{
    let n = if values.len() < 1 { 1usize } else if values.len() > 100 { 100usize } else { values.len() };
    let width = if values.len() > 0 { values[0].len() } else { 1usize };
    let cols = if width < 1 { 1usize } else if width > 100 { 100usize } else { width };
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r = 0usize;
    while r < n
        invariant
            1 <= n <= 100,
            1 <= cols <= 100,

            0 <= r <= n,
            grid.len() == r,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
            forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < cols ==> -100 <= #[trigger] grid[i][j] <= 100,
            forall|r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() - 1 ==> #[trigger] grid[r][c] >= grid[r][c + 1],
            forall|r: int, c: int| 0 <= r < grid.len() - 1 && 0 <= c < grid[r].len() ==> #[trigger] grid[r][c] >= grid[r + 1][c],
        decreases n - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c = 0usize;
        while c < cols
            invariant
                1 <= n <= 100,
                0 <= r < n,
                1 <= cols <= 100,
                0 <= c <= cols,
                row.len() == c,
                grid.len() == r,
                forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
                forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < cols ==> -100 <= #[trigger] grid[i][j] <= 100,
                forall|j: int| 0 <= j < row.len() ==> -100 <= #[trigger] row[j] <= 100,
                forall|j: int| 0 <= j < row.len() - 1 ==> #[trigger] row[j] >= row[j + 1],
                forall|j: int| r > 0 && 0 <= j < row.len() ==> grid[r - 1][j] >= #[trigger] row[j],
            decreases cols - c,
        {
            let value = if r < values.len() && c < values[r].len() { values[r][c] } else { -100 };
            let mut value = if value < -100 { -100 } else if value > 100 { 100 } else { value };
            if c > 0 && value > row[c - 1] { value = row[c - 1]; }
            if r > 0 {
                assert(grid[(r - 1) as int].len() == cols);
                let previous = &grid[r - 1];
                if value > previous[c] { value = previous[c]; }
            }
            row.push(value);
            c += 1;
        }
        grid.push(row);
        r += 1;
    }
    grid
}


pub fn generate_candidate(
    m: usize,
    n: usize,
    values: &Vec<Vec<i32>>,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= m <= 100,
        1 <= n <= 100,
        values.len() == m,
        forall |r: int| 0 <= r < values.len() ==> (#[trigger] values[r]).len() == n,
        forall |r: int, c: int| 0 <= r < values.len() && 0 <= c < values[r].len() ==>
            -100 <= #[trigger] values[r][c] <= 100,
    ensures
        1 <= grid.len() <= 100,
        forall |r: int| 0 <= r < grid.len() ==> 1 <= (#[trigger] grid[r]).len() <= 100,
        forall |r: int| 0 <= r < grid.len() ==> (#[trigger] grid[r]).len() == grid[0].len(),
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==>
            -100 <= #[trigger] grid[r][c] <= 100,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            1 <= m <= 100,
            1 <= n <= 100,
            values.len() == m,
            forall |r: int| 0 <= r < values.len() ==> (#[trigger] values[r]).len() == n,
            forall |r: int, c: int| 0 <= r < values.len() && 0 <= c < values[r].len() ==>
                -100 <= #[trigger] values[r][c] <= 100,
            0 <= i <= m,
            grid.len() == i,
            forall |r: int| 0 <= r < grid.len() ==> (#[trigger] grid[r]).len() == n,
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==>
                -100 <= #[trigger] grid[r][c] <= 100,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        let src = &values[i];
        assert(src.len() == n);

        while j < n
            invariant
                1 <= n <= 100,
                0 <= j <= n,
                row.len() == j,
                src.len() == n,
                i < m,
                forall |c: int| 0 <= c < src.len() ==> -100 <= #[trigger] src[c] <= 100,
                forall |c: int| 0 <= c < row.len() ==> row[c] == src[c],
                forall |c: int| 0 <= c < row.len() ==> -100 <= #[trigger] row[c] <= 100,
            decreases n - j,
        {
            row.push(src[j]);
            j += 1;
        }

        grid.push(row);
        i += 1;
    }

    proof {
        assert(grid.len() == m);
        assert(grid[0].len() == n);
        assert forall |r: int| 0 <= r < grid.len() implies 1 <= (#[trigger] grid[r]).len() <= 100 by {
            assert(grid[r].len() == n);
        }
        assert forall |r: int| 0 <= r < grid.len() implies (#[trigger] grid[r]).len() == grid[0].len() by {
            assert(grid[r].len() == n);
            assert(grid[0].len() == n);
        }
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
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_sorted_grid(rng: &mut Rng, m: usize, n: usize, mode: usize) -> Vec<Vec<i32>> {
    // Generate sorted non-increasing in both directions. We'll just generate any values in [-100, 100].
    // The spec only requires values in [-100, 100]; sorting isn't enforced by requires.
    let mut grid: Vec<Vec<i32>> = Vec::with_capacity(m);
    match mode {
        0 => {
            // all negative
            for _ in 0..m {
                let mut row = Vec::with_capacity(n);
                for _ in 0..n {
                    row.push(rng.range_i32(-100, -1));
                }
                grid.push(row);
            }
        }
        1 => {
            // all non-negative
            for _ in 0..m {
                let mut row = Vec::with_capacity(n);
                for _ in 0..n {
                    row.push(rng.range_i32(0, 100));
                }
                grid.push(row);
            }
        }
        2 => {
            // all zeros
            for _ in 0..m {
                let mut row = Vec::with_capacity(n);
                for _ in 0..n {
                    row.push(0);
                }
                grid.push(row);
            }
        }
        3 => {
            // boundary values
            for _ in 0..m {
                let mut row = Vec::with_capacity(n);
                for _ in 0..n {
                    let choice = rng.range_usize(0, 2);
                    let v = match choice { 0 => -100, 1 => 0, _ => 100 };
                    row.push(v);
                }
                grid.push(row);
            }
        }
        4 => {
            // sorted non-increasing
            let mut base: Vec<Vec<i32>> = Vec::with_capacity(m);
            for i in 0..m {
                let mut row = Vec::with_capacity(n);
                for j in 0..n {
                    let v = 100 - (i as i32 + j as i32) * 2;
                    let v = if v < -100 { -100 } else if v > 100 { 100 } else { v };
                    row.push(v);
                }
                base.push(row);
            }
            grid = base;
        }
        5 => {
            // diagonal flip
            for i in 0..m {
                let mut row = Vec::with_capacity(n);
                for j in 0..n {
                    let v: i32 = if (i + j) as i32 >= ((m + n) as i32) / 2 { -1 } else { 1 };
                    row.push(v);
                }
                grid.push(row);
            }
        }
        6 => {
            // all -100
            for _ in 0..m {
                let mut row = Vec::with_capacity(n);
                for _ in 0..n {
                    row.push(-100);
                }
                grid.push(row);
            }
        }
        7 => {
            // all 100
            for _ in 0..m {
                let mut row = Vec::with_capacity(n);
                for _ in 0..n {
                    row.push(100);
                }
                grid.push(row);
            }
        }
        8 => {
            // random
            for _ in 0..m {
                let mut row = Vec::with_capacity(n);
                for _ in 0..n {
                    row.push(rng.range_i32(-100, 100));
                }
                grid.push(row);
            }
        }
        _ => {
            // alternating
            for i in 0..m {
                let mut row = Vec::with_capacity(n);
                for j in 0..n {
                    let v: i32 = if (i + j) % 2 == 0 { -1 } else { 1 };
                    row.push(v);
                }
                grid.push(row);
            }
        }
    }
    grid
}

fn print_json(grid: &Vec<Vec<i32>>) {
    let grid = generate_test_case(grid.clone());
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
        let (m, n): (usize, usize) = match t % 7 {
            0 => (1, 1),
            1 => (1, 100),
            2 => (100, 1),
            3 => (100, 100),
            4 => (rng.range_usize(1, 10), rng.range_usize(1, 10)),
            5 => (rng.range_usize(1, 100), rng.range_usize(1, 100)),
            _ => (rng.range_usize(1, 50), rng.range_usize(1, 50)),
        };

        let values = make_sorted_grid(&mut rng, m, n, mode);
        let grid = generate_candidate(m, n, &values);
        print_json(&grid);
    }
}
