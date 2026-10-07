use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<Vec<i32>>) -> (grid: Vec<Vec<i32>>)
    ensures
        3 <= grid.len() <= 100,
        forall|r: int| 0 <= r < grid.len() ==> 1 <= #[trigger] grid[r].len() <= 100,
        forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid.len(),
        forall|r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 100000,

{
    let n = if values.len() < 3 { 3usize } else if values.len() > 100 { 100usize } else { values.len() };
    let cols = n;
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r = 0usize;
    while r < n
        invariant
            3 <= n <= 100,
            1 <= cols <= 100,
            cols == n,
            0 <= r <= n,
            grid.len() == r,
            forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
            forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < cols ==> 0 <= #[trigger] grid[i][j] <= 100000,

        decreases n - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c = 0usize;
        while c < cols
            invariant
                3 <= n <= 100,
                0 <= r < n,
                1 <= cols <= 100,
                0 <= c <= cols,
                row.len() == c,
                grid.len() == r,
                forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
                forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < cols ==> 0 <= #[trigger] grid[i][j] <= 100000,
                forall|j: int| 0 <= j < row.len() ==> 0 <= #[trigger] row[j] <= 100000,

            decreases cols - c,
        {
            let value = if r < values.len() && c < values[r].len() { values[r][c] } else { 0 };
            let mut value = if value < 0 { 0 } else if value > 100000 { 100000 } else { value };

            row.push(value);
            c += 1;
        }
        grid.push(row);
        r += 1;
    }
    grid
}


pub fn generate_candidate(
    n: usize,
    diag_vals: &Vec<Vec<i32>>,
) -> (grid: Vec<Vec<i32>>)
    requires
        3 <= n <= 100,
        diag_vals.len() == n,
        forall |i: int| 0 <= i < n ==> (#[trigger] diag_vals[i]).len() == n,
        forall |i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            1 <= #[trigger] (diag_vals[i])[j] <= 100000,
    ensures
        grid.len() == n,
        1 <= grid.len() <= 100,
        forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() ==>
            0 <= #[trigger] (grid[i])[j] <= 100000,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            3 <= n <= 100,
            diag_vals.len() == n,
            forall |a: int| 0 <= a < n ==> (#[trigger] diag_vals[a]).len() == n,
            forall |a: int, b: int| 0 <= a < n && 0 <= b < n ==>
                1 <= #[trigger] (diag_vals[a])[b] <= 100000,
            i <= n,
            grid.len() == i,
            forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == n,
            forall |r: int, c: int| 0 <= r < i && 0 <= c < n ==>
                0 <= #[trigger] (grid[r])[c] <= 100000,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                3 <= n <= 100,
                i < n,
                diag_vals.len() == n,
                forall |a: int| 0 <= a < n ==> (#[trigger] diag_vals[a]).len() == n,
                forall |a: int, b: int| 0 <= a < n && 0 <= b < n ==>
                    1 <= #[trigger] (diag_vals[a])[b] <= 100000,
                j <= n,
                row.len() == j,
                forall |c: int| 0 <= c < j ==>
                    0 <= #[trigger] row[c] <= 100000,
            decreases n - j,
        {
            let is_diag = (i == j) || (i + j == n - 1);
            let v: i32 = if is_diag {
                diag_vals[i][j]
            } else {
                0
            };
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_diag_vals(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut out: Vec<Vec<i32>> = Vec::new();
    for _ in 0..n {
        let mut row: Vec<i32> = Vec::new();
        for _ in 0..n {
            row.push(rng.gen_range_i32(1, 100000));
        }
        out.push(row);
    }
    out
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let n = match mode {
            0 => 3,
            1 => 4,
            2 => 5,
            3 => 100,
            4 => 99,
            5 => 50,
            6 => 10,
            7 => rng.gen_range_usize(3, 100),
            8 => rng.gen_range_usize(3, 20),
            9 => rng.gen_range_usize(3, 100),
            _ => rng.gen_range_usize(3, 100),
        };

        let diag_vals = make_diag_vals(&mut rng, n);
        let grid = generate_candidate(n, &diag_vals);
        print_json(&grid);
    }
}
