use vstd::prelude::*;

verus! {

pub fn generate_test_case(m: usize, n: usize, fill: i32) -> (matrix: Vec<Vec<i32>>)
    requires
        1 <= m <= 1_000,
        1 <= n <= 1_000,
        m * n <= 100_000,
        -1_000_000_000 <= fill <= 1_000_000_000,
    ensures
        1 <= matrix.len() <= 1_000,
        matrix.len() == m,
        1 <= matrix[0].len() <= 1_000,
        matrix[0].len() == n,
        forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
        matrix.len() * matrix[0].len() <= 100_000,
        forall |r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==> -1_000_000_000 <= #[trigger] matrix[r][c] <= 1_000_000_000,
{
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < m
        invariant
            0 <= r <= m,
            matrix.len() == r,
            1 <= m <= 1_000,
            1 <= n <= 1_000,
            -1_000_000_000 <= fill <= 1_000_000_000,
            forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == n,
            forall |i: int, c: int| 0 <= i < matrix.len() && 0 <= c < matrix[i].len() ==> -1_000_000_000 <= #[trigger] matrix[i][c] <= 1_000_000_000,
        decreases m - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < n
            invariant
                0 <= c <= n,
                row.len() == c,
                1 <= n <= 1_000,
                -1_000_000_000 <= fill <= 1_000_000_000,
                forall |k: int| 0 <= k < row.len() ==> -1_000_000_000 <= #[trigger] row[k] <= 1_000_000_000,
            decreases n - c,
        {
            row.push(fill);
            c = c + 1;
        }
        matrix.push(row);
        r = r + 1;
    }
    matrix
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(1) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_dims(rng: &mut Rng, mode: usize) -> (usize, usize) {
    match mode {
        0 => (1, 1),
        1 => (1, 1000),
        2 => (1000, 1),
        3 => (100, 1000),
        4 => (1000, 100),
        5 => (316, 316),
        6 => (2, 2),
        7 => (rng.gen_usize(1, 10), rng.gen_usize(1, 10)),
        8 => (rng.gen_usize(1, 100), rng.gen_usize(1, 100)),
        9 => {
            let m = rng.gen_usize(1, 1000);
            let max_n = if m == 0 { 1 } else { 100_000 / m };
            let hi = if max_n > 1000 { 1000 } else if max_n < 1 { 1 } else { max_n };
            (m, rng.gen_usize(1, hi))
        }
        _ => {
            let n = rng.gen_usize(1, 1000);
            let max_m = 100_000 / n;
            let hi = if max_m > 1000 { 1000 } else if max_m < 1 { 1 } else { max_m };
            (rng.gen_usize(1, hi), n)
        }
    }
}

fn pick_fill(rng: &mut Rng, mode: usize) -> i32 {
    match mode % 5 {
        0 => 0,
        1 => 1_000_000_000,
        2 => -1_000_000_000,
        3 => rng.gen_i32(-1_000_000_000, 1_000_000_000),
        _ => rng.gen_i32(-100, 100),
    }
}

fn print_matrix(matrix: &Vec<Vec<i32>>) {
    print!("{{\"matrix\":[");
    for i in 0..matrix.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..matrix[i].len() {
            if j > 0 { print!(","); }
            print!("{}", matrix[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n) = pick_dims(&mut rng, mode);
        let fill = pick_fill(&mut rng, t);
        if (m as u64) * (n as u64) > 100_000 { continue; }
        if m < 1 || m > 1000 || n < 1 || n > 1000 { continue; }
        let matrix = generate_test_case(m, n, fill);
        print_matrix(&matrix);
    }
}