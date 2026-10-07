use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    values: &Vec<Vec<i32>>,
) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= m <= 6,
        1 <= n <= 6,
        values.len() == m,
        forall|i: int| 0 <= i < values.len() ==> (#[trigger] values[i]).len() == n,
        forall|i: int, j: int| 0 <= i < values.len() && 0 <= j < values[i].len() ==> 1 <= #[trigger] values[i][j] <= 9,
    ensures
        1 <= mat.len() <= 6,
        forall|i: int| 0 <= i < mat.len() ==> 1 <= (#[trigger] mat[i]).len() <= 6,
        forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == mat[0].len(),
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==> 1 <= #[trigger] mat[i][j] <= 9,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            1 <= m <= 6,
            1 <= n <= 6,
            values.len() == m,
            mat.len() == i,
            i <= m,
            forall|k: int| 0 <= k < values.len() ==> (#[trigger] values[k]).len() == n,
            forall|k: int, j: int| 0 <= k < values.len() && 0 <= j < values[k].len() ==> 1 <= #[trigger] values[k][j] <= 9,
            forall|k: int| 0 <= k < mat.len() ==> (#[trigger] mat[k]).len() == n,
            forall|k: int, j: int| 0 <= k < mat.len() && 0 <= j < mat[k].len() ==> 1 <= #[trigger] mat[k][j] <= 9,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 6,
                row.len() == j,
                j <= n,
                i < values.len(),
                values[i as int].len() == n,
                forall|t: int| 0 <= t < values[i as int].len() ==> 1 <= #[trigger] values[i as int][t] <= 9,
                forall|t: int| 0 <= t < row.len() ==> 1 <= #[trigger] row[t] <= 9,
            decreases n - j,
        {
            let v = values[i][j];
            assert(1 <= v <= 9);
            row.push(v);
            j += 1;
        }
        mat.push(row);
        i += 1;
    }

    proof {
        assert(mat.len() == m);
        assert(mat[0].len() == n);
        assert forall|k: int| 0 <= k < mat.len() implies (#[trigger] mat[k]).len() == mat[0].len() by {
            assert(mat[k].len() == n);
        }
    }

    mat
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
}

fn build_values(m: usize, n: usize, cells: &[i32]) -> Vec<Vec<i32>> {
    let mut v: Vec<Vec<i32>> = Vec::with_capacity(m);
    for i in 0..m {
        let mut row: Vec<i32> = Vec::with_capacity(n);
        for j in 0..n {
            let c = cells[i * n + j];
            let c = if c < 1 { 1 } else if c > 9 { 9 } else { c };
            row.push(c);
        }
        v.push(row);
    }
    v
}

fn gen_random(rng: &mut Rng) -> (usize, usize, Vec<i32>) {
    let m = rng.gen_range_usize(1, 6);
    let n = rng.gen_range_usize(1, 6);
    let mut cells = Vec::with_capacity(m * n);
    for _ in 0..(m * n) {
        cells.push(rng.gen_range_usize(1, 9) as i32);
    }
    (m, n, cells)
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (usize, usize, Vec<i32>) {
    match mode {
        0 => {
            // 1x1
            let v = rng.gen_range_usize(1, 9) as i32;
            (1, 1, vec![v])
        }
        1 => {
            // All same digit
            let m = rng.gen_range_usize(1, 6);
            let n = rng.gen_range_usize(1, 6);
            let v = rng.gen_range_usize(1, 9) as i32;
            let cells = vec![v; m * n];
            (m, n, cells)
        }
        2 => {
            // Max 6x6, all 9s
            (6, 6, vec![9; 36])
        }
        3 => {
            // 6x6 all 1s
            (6, 6, vec![1; 36])
        }
        4 => {
            // 1xN row
            let n = rng.gen_range_usize(1, 6);
            let mut cells = Vec::with_capacity(n);
            for _ in 0..n {
                cells.push(rng.gen_range_usize(1, 9) as i32);
            }
            (1, n, cells)
        }
        5 => {
            // Mx1 column
            let m = rng.gen_range_usize(1, 6);
            let mut cells = Vec::with_capacity(m);
            for _ in 0..m {
                cells.push(rng.gen_range_usize(1, 9) as i32);
            }
            (m, 1, cells)
        }
        6 => {
            // Digits that form primes often: 1,3,7,9
            let m = rng.gen_range_usize(2, 6);
            let n = rng.gen_range_usize(2, 6);
            let choices = [1, 3, 7, 9];
            let mut cells = Vec::with_capacity(m * n);
            for _ in 0..(m * n) {
                cells.push(choices[rng.gen_range_usize(0, 3)]);
            }
            (m, n, cells)
        }
        7 => {
            // Even digits (rarely prime > 10)
            let m = rng.gen_range_usize(2, 6);
            let n = rng.gen_range_usize(2, 6);
            let choices = [2, 4, 6, 8];
            let mut cells = Vec::with_capacity(m * n);
            for _ in 0..(m * n) {
                cells.push(choices[rng.gen_range_usize(0, 3)]);
            }
            (m, n, cells)
        }
        8 => {
            // Alternating 1,9 pattern like example 1
            let m = rng.gen_range_usize(2, 6);
            let n = rng.gen_range_usize(2, 6);
            let mut cells = Vec::with_capacity(m * n);
            for i in 0..m {
                for _ in 0..n {
                    cells.push(if i % 2 == 0 { 1 } else { 9 });
                }
            }
            (m, n, cells)
        }
        9 => {
            // Example 3
            (3, 3, vec![9,7,8,4,6,5,2,8,6])
        }
        _ => gen_random(rng),
    }
}

fn print_json(mat: &[Vec<i32>]) {
    print!("{{\"mat\":[");
    for i in 0..mat.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..mat[i].len() {
            if j > 0 { print!(","); }
            print!("{}", mat[i][j]);
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
        let (m, n, cells) = gen_mode(&mut rng, mode);
        let values = build_values(m, n, &cells);
        let mat = generate_test_case(m, n, &values);
        print_json(&mat);
    }
}