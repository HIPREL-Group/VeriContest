use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    r: i32,
    c: i32,
    values: &Vec<i32>,
) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= m <= 100,
        1 <= n <= 100,
        1 <= r <= 300,
        1 <= c <= 300,
        values.len() == m * n,
        forall |k: int| 0 <= k < values.len() ==> -1_000 <= #[trigger] values[k] <= 1_000,
    ensures
        1 <= mat.len() <= 100,
        1 <= mat[0].len() <= 100,
        mat.len() == m,
        mat[0].len() == n,
        forall |k: int| 0 <= k < mat.len() ==> #[trigger] mat[k].len() == mat[0].len(),
        forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==> -1_000 <= #[trigger] mat[i][j] <= 1_000,
        mat.len() * mat[0].len() <= usize::MAX,
        r * c <= usize::MAX,
        1 <= r <= 300,
        1 <= c <= 300,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    assert(m * n <= 100 * 100) by (nonlinear_arith)
        requires m <= 100, n <= 100;

    while i < m
        invariant
            0 <= i <= m,
            1 <= m <= 100,
            1 <= n <= 100,
            values.len() == m * n,
            mat.len() == i,
            forall |k: int| 0 <= k < values.len() ==> -1_000 <= #[trigger] values[k] <= 1_000,
            forall |k: int| 0 <= k < i ==> #[trigger] mat[k].len() == n,
            forall |a: int, b: int| 0 <= a < i && 0 <= b < n ==> -1_000 <= #[trigger] mat[a][b] <= 1_000,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        assert(i * n + n <= m * n) by (nonlinear_arith)
            requires i < m, n >= 0;

        while j < n
            invariant
                0 <= j <= n,
                0 <= i < m,
                1 <= n <= 100,
                values.len() == m * n,
                i * n + n <= m * n,
                row.len() == j,
                forall |k: int| 0 <= k < values.len() ==> -1_000 <= #[trigger] values[k] <= 1_000,
                forall |k: int| 0 <= k < j ==> -1_000 <= #[trigger] row[k] <= 1_000,
            decreases n - j,
        {
            let idx: usize = i * n + j;
            assert(idx < values.len());
            row.push(values[idx]);
            j = j + 1;
        }

        mat.push(row);
        i = i + 1;
    }

    proof {
        assert(mat.len() == m);
        assert(mat[0].len() == n);
        assert(mat.len() * mat[0].len() == m * n);
        assert(m * n <= 10_000);
        assert(r * c <= 300 * 300) by (nonlinear_arith)
            requires r <= 300, c <= 300, r >= 1, c >= 1;
    }

    mat
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

fn build_values(rng: &mut Rng, m: usize, n: usize, mode: usize) -> Vec<i32> {
    let total = m * n;
    let mut v = Vec::with_capacity(total);
    for k in 0..total {
        let x = match mode {
            0 => rng.gen_range_i32(-1000, 1000),
            1 => 0i32,
            2 => 1000i32,
            3 => -1000i32,
            4 => (k as i32) % 1001,
            5 => if k % 2 == 0 { 1000 } else { -1000 },
            6 => rng.gen_range_i32(-10, 10),
            7 => (k as i32) - 500,
            _ => rng.gen_range_i32(-1000, 1000),
        };
        v.push(x);
    }
    v
}

fn pick_dims(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize, i32, i32) {
    match mode {
        0 => (1, 1, 1, 1),
        1 => (2, 2, 1, 4),
        2 => (2, 2, 4, 1),
        3 => (3, 4, 2, 6),
        4 => (3, 4, 5, 5), // not reshape-able
        5 => (100, 100, 300, 300), // mismatch
        6 => (100, 100, 200, 50), // 10000 = 10000
        7 => (1, 100, 100, 1),
        8 => (100, 1, 1, 100),
        9 => {
            let m = rng.gen_range_usize(1, 10);
            let n = rng.gen_range_usize(1, 10);
            let r = rng.gen_range_usize(1, 20) as i32;
            let c = rng.gen_range_usize(1, 20) as i32;
            (m, n, r, c)
        }
        _ => {
            let m = rng.gen_range_usize(1, 50);
            let n = rng.gen_range_usize(1, 50);
            let r = rng.gen_range_usize(1, 300) as i32;
            let c = rng.gen_range_usize(1, 300) as i32;
            let _ = t;
            (m, n, r, c)
        }
    }
}

fn print_json(mat: &Vec<Vec<i32>>, r: i32, c: i32) {
    print!("{{\"mat\":[");
    for i in 0..mat.len() {
        if i > 0 {
            print!(",");
        }
        print!("[");
        for j in 0..mat[i].len() {
            if j > 0 {
                print!(",");
            }
            print!("{}", mat[i][j]);
        }
        print!("]");
    }
    println!("],\"r\":{},\"c\":{}}}", r, c);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n, r, c) = pick_dims(&mut rng, mode, t);
        let val_mode = t % 8;
        let values = build_values(&mut rng, m, n, val_mode);
        let mat = generate_test_case(m, n, r, c, &values);
        print_json(&mat, r, c);
    }
}