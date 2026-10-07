use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    values: &Vec<i32>,
) -> (img: Vec<Vec<i32>>)
    requires
        1 <= m <= 200,
        1 <= n <= 200,
        values.len() == m * n,
        forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 255,
    ensures
        img.len() == m,
        1 <= img.len() <= 200,
        1 <= img[0].len() <= 200,
        forall|i: int| 0 <= i < img.len() ==> #[trigger] img[i].len() == img[0].len(),
        forall|i: int| 0 <= i < img.len() ==> #[trigger] img[i].len() == n,
        forall|i: int, j: int| 0 <= i < img.len() && 0 <= j < img[i].len() ==> 0 <= #[trigger] img[i][j] <= 255,
{
    let mut img: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            1 <= m <= 200,
            1 <= n <= 200,
            values.len() == m * n,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 255,
            0 <= i <= m,
            img.len() == i,
            forall|ii: int| 0 <= ii < img.len() ==> (#[trigger] img[ii]).len() == n,
            forall|ii: int, jj: int| 0 <= ii < img.len() && 0 <= jj < n ==> 0 <= #[trigger] img[ii][jj] <= 255,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        assert(i * n + n <= m * n) by (nonlinear_arith)
            requires i < m, n >= 0;

        while j < n
            invariant
                1 <= m <= 200,
                1 <= n <= 200,
                values.len() == m * n,
                forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 255,
                0 <= i < m,
                0 <= j <= n,
                row.len() == j,
                i * n + n <= m * n,
                forall|jj: int| 0 <= jj < row.len() ==> 0 <= #[trigger] row[jj] <= 255,
            decreases n - j,
        {
            let idx: usize = i * n + j;
            assert(idx < m * n);
            let v = values[idx];
            row.push(v);
            j = j + 1;
        }

        img.push(row);
        i = i + 1;
    }

    img
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

fn make_values(rng: &mut Rng, mode: usize, m: usize, n: usize) -> Vec<i32> {
    let size = m * n;
    let mut v = Vec::with_capacity(size);
    match mode {
        0 => {
            // all zeros
            for _ in 0..size { v.push(0); }
        }
        1 => {
            // all 255
            for _ in 0..size { v.push(255); }
        }
        2 => {
            // all same random
            let x = rng.gen_range_i32(0, 255);
            for _ in 0..size { v.push(x); }
        }
        3 => {
            // random 0-255
            for _ in 0..size { v.push(rng.gen_range_i32(0, 255)); }
        }
        4 => {
            // checkerboard 0/255
            for i in 0..m {
                for j in 0..n {
                    v.push(if (i + j) % 2 == 0 { 0 } else { 255 });
                }
            }
        }
        5 => {
            // gradient (row index based)
            for i in 0..m {
                for _j in 0..n {
                    v.push(((i * 255) / m.max(1)) as i32);
                }
            }
        }
        6 => {
            // gradient (col index based)
            for _i in 0..m {
                for j in 0..n {
                    v.push(((j * 255) / n.max(1)) as i32);
                }
            }
        }
        7 => {
            // bimodal 0 and 255 random
            for _ in 0..size {
                v.push(if rng.next_u64() % 2 == 0 { 0 } else { 255 });
            }
        }
        8 => {
            // mostly small values
            for _ in 0..size { v.push(rng.gen_range_i32(0, 10)); }
        }
        9 => {
            // mostly large values
            for _ in 0..size { v.push(rng.gen_range_i32(245, 255)); }
        }
        _ => {
            // random
            for _ in 0..size { v.push(rng.gen_range_i32(0, 255)); }
        }
    }
    v
}

fn print_json(img: &Vec<Vec<i32>>) {
    print!("{{\"img\":[");
    for i in 0..img.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..img[i].len() {
            if j > 0 { print!(","); }
            print!("{}", img[i][j]);
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
        // Pick dimensions with various sizes
        let (m, n) = match t % 13 {
            0 => (1usize, 1usize),
            1 => (1usize, 200usize),
            2 => (200usize, 1usize),
            3 => (200usize, 200usize),
            4 => (1usize, rng.gen_range_usize(1, 200)),
            5 => (rng.gen_range_usize(1, 200), 1usize),
            6 => (2usize, 2usize),
            7 => (3usize, 3usize),
            8 => (rng.gen_range_usize(1, 10), rng.gen_range_usize(1, 10)),
            9 => (rng.gen_range_usize(50, 100), rng.gen_range_usize(50, 100)),
            10 => (rng.gen_range_usize(1, 50), rng.gen_range_usize(150, 200)),
            11 => (rng.gen_range_usize(150, 200), rng.gen_range_usize(1, 50)),
            _ => (rng.gen_range_usize(1, 200), rng.gen_range_usize(1, 200)),
        };

        let values = make_values(&mut rng, mode, m, n);
        let img = generate_test_case(m, n, &values);
        print_json(&img);
    }
}