use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    values: &Vec<i32>,
    k: i32,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= m <= 50,
        1 <= n <= 50,
        values.len() == m * n,
        forall|i: int| 0 <= i < values.len() ==> -1000 <= #[trigger] values[i] <= 1000,
        0 <= k <= 100,
    ensures
        ({
            let grid = result.0;
            let kk = result.1;
            &&& kk == k
            &&& 1 <= grid.deep_view().len() <= 50
            &&& forall|i: int| 0 <= i < grid.deep_view().len() ==>
                    1 <= (#[trigger] grid.deep_view()[i]).len() <= 50
            &&& forall|i: int| 0 <= i < grid.deep_view().len() ==>
                    (#[trigger] grid.deep_view()[i]).len() == grid.deep_view()[0].len()
            &&& forall|i: int, j: int|
                    0 <= i < grid.deep_view().len() && 0 <= j < grid.deep_view()[i].len() ==>
                        -1000 <= #[trigger] grid.deep_view()[i][j] <= 1000
            &&& 0 <= kk <= 100
        }),
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            1 <= m <= 50,
            1 <= n <= 50,
            values.len() == m * n,
            i <= m,
            grid.len() == i,
            forall|a: int| 0 <= a < i ==> (#[trigger] grid[a]).len() == n,
            forall|a: int, b: int| 0 <= a < i && 0 <= b < n as int ==>
                -1000 <= #[trigger] grid[a][b] <= 1000,
            forall|p: int| 0 <= p < values.len() ==> -1000 <= #[trigger] values[p] <= 1000,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        // Establish bound: i * n + n <= m * n
        assert(i < m);
        assert((i + 1) * n == i * n + n) by (nonlinear_arith);
        assert((i + 1) * n <= m * n) by (nonlinear_arith) requires i + 1 <= m, n >= 0;

        while j < n
            invariant
                1 <= m <= 50,
                1 <= n <= 50,
                values.len() == m * n,
                i < m,
                j <= n,
                row.len() == j,
                (i + 1) * n <= m * n,
                i * n + n == (i + 1) * n,
                forall|b: int| 0 <= b < j as int ==>
                    -1000 <= #[trigger] row[b] <= 1000,
                forall|p: int| 0 <= p < values.len() ==> -1000 <= #[trigger] values[p] <= 1000,
            decreases n - j,
        {
            let idx: usize = i * n + j;
            assert(idx < values.len()) by (nonlinear_arith)
                requires
                    idx == i * n + j,
                    j < n,
                    (i + 1) * n <= m * n,
                    i * n + n == (i + 1) * n,
                    values.len() == m * n;
            let v: i32 = values[idx];
            row.push(v);
            j = j + 1;
        }

        grid.push(row);
        i = i + 1;
    }

    proof {
        assert(grid.deep_view().len() == grid.len());
        assert(grid.len() == m);
        assert forall|a: int| 0 <= a < grid.deep_view().len() implies
            (#[trigger] grid.deep_view()[a]).len() == n
        by {
            assert(grid.deep_view()[a] == grid[a].deep_view());
            assert(grid[a].deep_view().len() == grid[a].len());
        }
        assert forall|a: int| 0 <= a < grid.deep_view().len() implies
            1 <= (#[trigger] grid.deep_view()[a]).len() <= 50
        by {
            assert(grid.deep_view()[a].len() == n);
        }
        assert(grid.deep_view()[0].len() == n);
        assert forall|a: int| 0 <= a < grid.deep_view().len() implies
            (#[trigger] grid.deep_view()[a]).len() == grid.deep_view()[0].len()
        by {
            assert(grid.deep_view()[a].len() == n);
            assert(grid.deep_view()[0].len() == n);
        }
        assert forall|a: int, b: int|
            0 <= a < grid.deep_view().len() && 0 <= b < grid.deep_view()[a].len() implies
                -1000 <= #[trigger] grid.deep_view()[a][b] <= 1000
        by {
            assert(grid.deep_view()[a] == grid[a].deep_view());
            assert(grid.deep_view()[a][b] == grid[a][b]);
        }
    }

    (grid, k)
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

fn build_values(rng: &mut Rng, m: usize, n: usize, mode: usize) -> Vec<i32> {
    let total = m * n;
    let mut v: Vec<i32> = Vec::with_capacity(total);
    for i in 0..total {
        let x = match mode {
            0 => rng.gen_range_i32(-1000, 1000),
            1 => 0i32,
            2 => 1000i32,
            3 => -1000i32,
            4 => i as i32 % 1001 - 500,
            5 => if i % 2 == 0 { 1000 } else { -1000 },
            6 => (i as i32) - (total as i32 / 2),
            7 => rng.gen_range_i32(-10, 10),
            8 => if rng.next_u64() % 2 == 0 { 1000 } else { -1000 },
            9 => rng.gen_range_i32(-1000, 1000),
            _ => rng.gen_range_i32(-1000, 1000),
        };
        let x = if x > 1000 { 1000 } else if x < -1000 { -1000 } else { x };
        v.push(x);
    }
    v
}

fn print_json(grid: &[Vec<i32>], k: i32) {
    print!("{{\"grid\":[");
    for (i, row) in grid.iter().enumerate() {
        if i > 0 { print!(","); }
        print!("[");
        for (j, val) in row.iter().enumerate() {
            if j > 0 { print!(","); }
            print!("{}", val);
        }
        print!("]");
    }
    println!("],\"k\":{}}}", k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total_tests = 200usize;

    for t in 0..total_tests {
        let mode = t % 10;

        let (m, n, k) = match mode {
            0 => (1usize, 1usize, 0i32),
            1 => (1, 1, 100),
            2 => (50, 50, 100),
            3 => (1, 50, rng.gen_range_i32(0, 100)),
            4 => (50, 1, rng.gen_range_i32(0, 100)),
            5 => (
                rng.gen_range_usize(1, 50),
                rng.gen_range_usize(1, 50),
                0,
            ),
            6 => {
                let m = rng.gen_range_usize(1, 10);
                let n = rng.gen_range_usize(1, 10);
                (m, n, (m * n) as i32)
            }
            7 => {
                let m = rng.gen_range_usize(1, 10);
                let n = rng.gen_range_usize(1, 10);
                let mn = (m * n) as i32;
                let k = if mn > 100 { 100 } else { mn };
                (m, n, k)
            }
            8 => (3, 3, 1),
            9 => (4, 4, 4),
            _ => (
                rng.gen_range_usize(1, 50),
                rng.gen_range_usize(1, 50),
                rng.gen_range_i32(0, 100),
            ),
        };

        let k = if k < 0 { 0 } else if k > 100 { 100 } else { k };
        let values = build_values(&mut rng, m, n, mode);
        let (grid, kk) = generate_test_case(m, n, &values, k);
        print_json(&grid, kk);
    }
}