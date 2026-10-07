use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    values: &Vec<Vec<i32>>,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= m <= 1000,
        1 <= n <= 1000,
        values.len() == m,
        forall |i: int| 0 <= i < m ==> #[trigger] values[i].len() == n,
        forall |i: int, c: int| 0 <= i < m && 0 <= c < n ==> 0 <= #[trigger] values[i][c] <= 9,
    ensures
        1 <= grid.len() <= 1000,
        1 <= grid[0].len() <= 1000,
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 9,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            1 <= m <= 1000,
            1 <= n <= 1000,
            values.len() == m,
            forall |ii: int| 0 <= ii < m ==> #[trigger] values[ii].len() == n,
            forall |ii: int, c: int| 0 <= ii < m && 0 <= c < n ==> 0 <= #[trigger] values[ii][c] <= 9,
            0 <= i <= m,
            grid.len() == i,
            forall |r: int| 0 <= r < i ==> #[trigger] grid[r].len() == n,
            forall |r: int, c: int| 0 <= r < i && 0 <= c < n ==> 0 <= #[trigger] grid[r][c] <= 9,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 1000,
                0 <= i < m,
                values.len() == m,
                values[i as int].len() == n,
                forall |c: int| 0 <= c < n ==> 0 <= #[trigger] values[i as int][c] <= 9,
                0 <= j <= n,
                row.len() == j,
                forall |c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 9,
            decreases n - j,
        {
            let v = values[i][j];
            assert(0 <= v <= 9);
            row.push(v);
            j = j + 1;
        }
        assert(row.len() == n);
        grid.push(row);
        i = i + 1;
    }

    assert(grid.len() == m);
    assert(grid[0].len() == n);

    grid
}

}

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

    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn make_values(rng: &mut Rng, m: usize, n: usize, mode: usize) -> Vec<Vec<i32>> {
    let mut values: Vec<Vec<i32>> = Vec::with_capacity(m);
    for i in 0..m {
        let mut row: Vec<i32> = Vec::with_capacity(n);
        for j in 0..n {
            let v: i32 = match mode {
                0 => rng.gen_i32(0, 9),
                1 => 0,
                2 => 9,
                3 => ((i + j) % 10) as i32,
                4 => ((j % 2) as i32),
                5 => ((j % 3) as i32),
                6 => (j as i32) % 10,
                7 => {
                    // already correct: grid[i][j] == grid[i+1][j], grid[i][j]!=grid[i][j+1]
                    ((j % 10) as i32)
                }
                8 => {
                    // rows all equal constant per row -> heavy ops
                    ((i % 10) as i32)
                }
                9 => {
                    if rng.next_u64() % 2 == 0 { 0 } else { 1 }
                }
                _ => rng.gen_i32(0, 9),
            };
            row.push(v);
        }
        values.push(row);
    }
    values
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n) = match mode {
            0 => (rng.gen_range_usize(1, 10), rng.gen_range_usize(1, 10)),
            1 => (1usize, rng.gen_range_usize(1, 50)),
            2 => (rng.gen_range_usize(1, 50), 1usize),
            3 => (rng.gen_range_usize(2, 20), rng.gen_range_usize(2, 20)),
            4 => (1000usize, 1usize),
            5 => (1usize, 1000usize),
            6 => (rng.gen_range_usize(30, 50), rng.gen_range_usize(30, 50)),
            7 => (rng.gen_range_usize(5, 15), rng.gen_range_usize(5, 15)),
            8 => (rng.gen_range_usize(5, 15), rng.gen_range_usize(5, 15)),
            9 => (rng.gen_range_usize(1, 5), rng.gen_range_usize(1, 5)),
            _ => (rng.gen_range_usize(1, 30), rng.gen_range_usize(1, 30)),
        };

        let values = make_values(&mut rng, m, n, mode);
        let grid = generate_test_case(m, n, &values);
        print_json(&grid);
    }
}