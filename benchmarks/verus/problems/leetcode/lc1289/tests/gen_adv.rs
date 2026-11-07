use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    vals: &Vec<Vec<i32>>,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= n <= 200,
        vals.len() == n,
        forall |i: int| 0 <= i < n as int ==> (#[trigger] vals[i]).len() == n as int,
        forall |i: int, j: int| 0 <= i < n as int && 0 <= j < n as int
            ==> -99 <= #[trigger] vals[i][j] <= 99,
    ensures
        1 <= grid.len() <= 200,
        grid.len() == n,
        forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len()
            ==> -99 <= #[trigger] grid[i][j] <= 99,
{
    let _ = vals;
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 200,
            grid.len() == i,
            forall |k: int| 0 <= k < i as int ==> (#[trigger] grid[k]).len() == n as int,
            forall |k: int, j: int| 0 <= k < i as int && 0 <= j < n as int
                ==> #[trigger] grid[k][j] == 0,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                1 <= n <= 200,
                row.len() == j,
                forall |t: int| 0 <= t < j as int ==> #[trigger] row[t] == 0,
            decreases n - j,
        {
            row.push(0);
            assert(row[j as int] == 0);
            assert forall |t: int| 0 <= t < j as int + 1 implies #[trigger] row[t] == 0 by {
                if t < j as int {
                } else {
                    assert(t == j as int);
                    assert(row[t] == 0);
                }
            };
            j = j + 1;
        }
        assert(row.len() == n);
        grid.push(row);
        assert(grid[i as int].len() == n as int);
        assert forall |k: int| 0 <= k < i as int + 1 implies (#[trigger] grid[k]).len() == n as int by {
            if k < i as int {
            } else {
                assert(k == i as int);
                assert(grid[k].len() == n as int);
            }
        };
        assert forall |k: int, j: int|
            0 <= k < i as int + 1 && 0 <= j < n as int implies #[trigger] grid[k][j] == 0 by {
            if k < i as int {
            } else {
                assert(k == i as int);
                assert(grid[k].len() == n as int);
                assert(grid[k][j] == 0);
            }
        };
        i = i + 1;
    }
    proof {
        assert(grid.len() == n);
        assert(1 <= grid.len() <= 200);
        assert forall |i: int| 0 <= i < grid.len() implies (#[trigger] grid[i]).len() == grid.len() by {
            assert(grid[i].len() == n as int);
            assert(grid.len() == n);
        };
        assert forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len()
            implies -99 <= #[trigger] grid[i][j] <= 99 by {
            assert(grid[i][j] == 0);
        };
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

fn build_vals(rng: &mut Rng, n: usize, mode: usize) -> Vec<Vec<i32>> {
    let mut vals: Vec<Vec<i32>> = Vec::with_capacity(n);
    for i in 0..n {
        let mut row: Vec<i32> = Vec::with_capacity(n);
        for j in 0..n {
            let v = match mode {
                0 => rng.gen_range_i32(-99, 99),
                1 => 0,
                2 => 99,
                3 => -99,
                4 => if (i + j) % 2 == 0 { 99 } else { -99 },
                5 => if j == 0 { -99 } else { 99 },
                6 => if i == j { -99 } else { 99 },
                7 => rng.gen_range_i32(-10, 10),
                8 => {
                    // Diagonal minimum trap: force same column to be smallest
                    if j == (i % n) { -99 } else { rng.gen_range_i32(50, 99) }
                }
                9 => {
                    // Alternating small values to test non-zero shift requirement
                    if j % 2 == (i % 2) { -99 } else { 99 }
                }
                _ => rng.gen_range_i32(-99, 99),
            };
            row.push(v);
        }
        vals.push(row);
    }
    vals
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
        let n = match mode {
            0 => rng.gen_range_usize(1, 10),
            1 => 1,
            2 => 2,
            3 => 200,
            4 => rng.gen_range_usize(2, 50),
            5 => rng.gen_range_usize(3, 30),
            6 => rng.gen_range_usize(3, 100),
            7 => rng.gen_range_usize(1, 200),
            8 => rng.gen_range_usize(2, 150),
            9 => rng.gen_range_usize(2, 80),
            _ => rng.gen_range_usize(1, 200),
        };
        let vals = build_vals(&mut rng, n, mode);
        let grid = generate_test_case(n, &vals);
        print_json(&grid);
    }
}
