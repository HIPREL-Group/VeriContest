use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, values: &Vec<i32>) -> (matrix: Vec<Vec<i32>>)
    requires
        2 <= n <= 250,
        values.len() == n * n,
        forall|k: int| 0 <= k < values.len() ==> -100_000 <= #[trigger] values[k] <= 100_000,
    ensures
        2 <= matrix.len() <= 250,
        matrix.len() == n,
        forall|r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix.len(),
        forall|r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==>
            -100_000 <= #[trigger] matrix[r][c] <= 100_000,
{
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;

    while r < n
        invariant
            2 <= n <= 250,
            values.len() == n * n,
            r <= n,
            matrix.len() == r,
            forall|i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == n,
            forall|i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len() ==>
                -100_000 <= #[trigger] matrix[i][j] <= 100_000,
            forall|k: int| 0 <= k < values.len() ==> -100_000 <= #[trigger] values[k] <= 100_000,
        decreases n - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;

        assert(r < n);
        assert(r * n + n <= n * n) by (nonlinear_arith) requires r < n, n <= 250;

        while c < n
            invariant
                2 <= n <= 250,
                values.len() == n * n,
                r < n,
                c <= n,
                row.len() == c,
                r * n + n <= n * n,
                forall|j: int| 0 <= j < row.len() ==>
                    -100_000 <= #[trigger] row[j] <= 100_000,
                forall|k: int| 0 <= k < values.len() ==> -100_000 <= #[trigger] values[k] <= 100_000,
            decreases n - c,
        {
            let idx: usize = r * n + c;
            assert(idx < n * n) by (nonlinear_arith)
                requires idx == r * n + c, c < n, r * n + n <= n * n;
            row.push(values[idx]);
            c = c + 1;
        }

        matrix.push(row);
        r = r + 1;
    }

    matrix
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

fn gen_values(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let total = n * n;
    let mut v = Vec::with_capacity(total);
    match mode {
        0 => {
            for _ in 0..total {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
        }
        1 => {
            for _ in 0..total {
                v.push(rng.gen_range_i32(-100_000, -1));
            }
        }
        2 => {
            for _ in 0..total {
                v.push(rng.gen_range_i32(1, 100_000));
            }
        }
        3 => {
            for _ in 0..total {
                v.push(0);
            }
        }
        4 => {
            for i in 0..total {
                v.push(if i % 2 == 0 { -100_000 } else { 100_000 });
            }
        }
        5 => {
            for _ in 0..total {
                let s = if rng.next_u64() % 2 == 0 { 1 } else { -1 };
                v.push(s * 100_000);
            }
        }
        6 => {
            for i in 0..total {
                if i == 0 {
                    v.push(-1);
                } else {
                    v.push(rng.gen_range_i32(1, 100_000));
                }
            }
        }
        7 => {
            for i in 0..total {
                if i == 0 {
                    v.push(1);
                } else {
                    v.push(-rng.gen_range_i32(1, 100_000));
                }
            }
        }
        8 => {
            let mut neg_count = 0;
            for _ in 0..total {
                let x = rng.gen_range_i32(-100_000, 100_000);
                if x < 0 { neg_count += 1; }
                v.push(x);
            }
            if neg_count % 2 != 0 && !v.is_empty() {
                v[0] = -v[0];
            }
        }
        9 => {
            for _ in 0..total {
                let x = rng.gen_range_i32(-3, 3);
                v.push(x);
            }
        }
        _ => {
            for _ in 0..total {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
        }
    }
    v
}

fn print_json(matrix: &Vec<Vec<i32>>) {
    print!("{{\"matrix\":[");
    for r in 0..matrix.len() {
        if r > 0 { print!(","); }
        print!("[");
        for c in 0..matrix[r].len() {
            if c > 0 { print!(","); }
            print!("{}", matrix[r][c]);
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
        let n = match t % 7 {
            0 => 2,
            1 => 3,
            2 => 4,
            3 => rng.gen_range_usize(2, 10),
            4 => rng.gen_range_usize(10, 50),
            5 => rng.gen_range_usize(50, 150),
            _ => rng.gen_range_usize(200, 250),
        };

        let values = gen_values(&mut rng, n, mode);
        let matrix = generate_test_case(n, &values);
        print_json(&matrix);
    }
}