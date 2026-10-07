use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    x: usize,
    y: usize,
    k: usize,
    vals: &Vec<Vec<i32>>,
) -> (res: (Vec<Vec<i32>>, i32, i32, i32))
    requires
        1 <= m <= 50,
        1 <= n <= 50,
        x < m,
        y < n,
        1 <= k,
        k <= m - x,
        k <= n - y,
        m <= 2147483647,
        n <= 2147483647,
        x <= 2147483647,
        y <= 2147483647,
        k <= 2147483647,
        vals.len() == m,
        forall |r: int| 0 <= r < vals.len() ==> #[trigger] vals[r].len() == n,
        forall |r: int, c: int| 0 <= r < vals.len() && 0 <= c < vals[r].len() ==> 1 <= #[trigger] vals[r][c] <= 100,
    ensures
        ({
            let grid = res.0;
            let xx = res.1;
            let yy = res.2;
            let kk = res.3;
            &&& 1 <= grid.len() <= 50
            &&& 1 <= grid[0].len() <= 50
            &&& (forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len())
            &&& (forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 100)
            &&& 0 <= (xx as int)
            &&& (xx as int) < grid.len()
            &&& 0 <= (yy as int)
            &&& (yy as int) < grid[0].len()
            &&& 1 <= (kk as int)
            &&& (kk as int) <= grid.len() - (xx as int)
            &&& (kk as int) <= grid[0].len() - (yy as int)
        }),
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            grid.len() == i,
            i <= m,
            vals.len() == m,
            forall |r: int| 0 <= r < vals.len() ==> #[trigger] vals[r].len() == n,
            forall |r: int, c: int| 0 <= r < vals.len() && 0 <= c < vals[r].len() ==> 1 <= #[trigger] vals[r][c] <= 100,
            forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == n,
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 100,
        decreases m - i,
    {
        let row = &vals[i];
        let mut new_row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                new_row.len() == j,
                j <= n,
                row.len() == n,
                forall |c: int| 0 <= c < row.len() ==> 1 <= #[trigger] row[c] <= 100,
                forall |c: int| 0 <= c < new_row.len() ==> 1 <= #[trigger] new_row[c] <= 100,
            decreases n - j,
        {
            new_row.push(row[j]);
            j = j + 1;
        }
        grid.push(new_row);
        i = i + 1;
    }

    assert(grid.len() == m);
    assert(grid[0].len() == n);

    (grid, x as i32, y as i32, k as i32)
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
    fn range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn gen_vals(rng: &mut Rng, m: usize, n: usize) -> Vec<Vec<i32>> {
    let mut v = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.range(1, 100) as i32);
        }
        v.push(row);
    }
    v
}

fn print_json(grid: &Vec<Vec<i32>>, x: i32, y: i32, k: i32) {
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
    println!("],\"x\":{},\"y\":{},\"k\":{}}}", x, y, k);
}

fn emit(rng: &mut Rng, m: usize, n: usize, x: usize, y: usize, k: usize) {
    let max_k_row = m - x;
    let max_k_col = n - y;
    let max_k = if max_k_row < max_k_col { max_k_row } else { max_k_col };
    let kk = if k < 1 { 1 } else if k > max_k { max_k } else { k };
    let vals = gen_vals(rng, m, n);
    let (grid, xi, yi, ki) = generate_test_case(m, n, x, y, kk, &vals);
    print_json(&grid, xi, yi, ki);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 220usize;
    for t in 0..total {
        let mode = t % 11;
        match mode {
            0 => {
                // minimal
                emit(&mut rng, 1, 1, 0, 0, 1);
            }
            1 => {
                // max size, full flip
                emit(&mut rng, 50, 50, 0, 0, 50);
            }
            2 => {
                // k = 1 (no-op)
                let m = rng.range(1, 50);
                let n = rng.range(1, 50);
                let x = rng.range(0, m - 1);
                let y = rng.range(0, n - 1);
                emit(&mut rng, m, n, x, y, 1);
            }
            3 => {
                // top-left corner
                let m = rng.range(2, 50);
                let n = rng.range(2, 50);
                let maxk = if m < n { m } else { n };
                let k = rng.range(1, maxk);
                emit(&mut rng, m, n, 0, 0, k);
            }
            4 => {
                // bottom-right corner
                let m = rng.range(2, 50);
                let n = rng.range(2, 50);
                let maxk = if m < n { m } else { n };
                let k = rng.range(1, maxk);
                emit(&mut rng, m, n, m - k, n - k, k);
            }
            5 => {
                // single row matrix
                let n = rng.range(1, 50);
                let y = rng.range(0, n - 1);
                let k = rng.range(1, n - y);
                let k = if k > 1 { 1 } else { k };
                emit(&mut rng, 1, n, 0, y, k);
            }
            6 => {
                // single column matrix
                let m = rng.range(1, 50);
                let x = rng.range(0, m - 1);
                let k = rng.range(1, m - x);
                let k = if k > 1 { 1 } else { k };
                emit(&mut rng, m, 1, x, 0, k);
            }
            7 => {
                // square grid with k covering whole
                let n = rng.range(2, 50);
                emit(&mut rng, n, n, 0, 0, n);
            }
            8 => {
                // k equals 2 (smallest actual flip)
                let m = rng.range(2, 50);
                let n = rng.range(2, 50);
                let x = rng.range(0, m - 2);
                let y = rng.range(0, n - 2);
                emit(&mut rng, m, n, x, y, 2);
            }
            9 => {
                // odd k
                let m = rng.range(3, 50);
                let n = rng.range(3, 50);
                let maxk_r = if m < n { m } else { n };
                let mut k = rng.range(1, maxk_r);
                if k % 2 == 0 { k = if k > 1 { k - 1 } else { 1 }; }
                let x = rng.range(0, m - k);
                let y = rng.range(0, n - k);
                emit(&mut rng, m, n, x, y, k);
            }
            _ => {
                // fully random
                let m = rng.range(1, 50);
                let n = rng.range(1, 50);
                let x = rng.range(0, m - 1);
                let y = rng.range(0, n - 1);
                let maxk_r = m - x;
                let maxk_c = n - y;
                let maxk = if maxk_r < maxk_c { maxk_r } else { maxk_c };
                let k = rng.range(1, maxk);
                emit(&mut rng, m, n, x, y, k);
            }
        }
    }
}