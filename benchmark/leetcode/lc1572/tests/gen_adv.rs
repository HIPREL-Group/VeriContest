use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, vals: &Vec<i32>) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= n <= 100,
        vals.len() == n * n,
        forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 100,
    ensures
        1 <= mat.len() <= 100,
        mat.len() == n,
        forall |i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == mat.len(),
        forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat.len() ==> 1 <= #[trigger] mat[i][j] <= 100,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            1 <= n <= 100,
            vals.len() == n * n,
            0 <= i <= n,
            mat.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 100,
            forall |a: int| 0 <= a < mat.len() ==> (#[trigger] mat[a]).len() == n,
            forall |a: int, b: int| 0 <= a < mat.len() && 0 <= b < n ==> 1 <= #[trigger] mat[a][b] <= 100,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        assert(i < n);
        assert(i * n + n <= n * n) by (nonlinear_arith)
            requires i < n, n <= 100;
        while j < n
            invariant
                1 <= n <= 100,
                vals.len() == n * n,
                i < n,
                0 <= j <= n,
                row.len() == j,
                i * n + n <= n * n,
                forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 100,
                forall |b: int| 0 <= b < row.len() ==> 1 <= #[trigger] row[b] <= 100,
            decreases n - j,
        {
            let idx: usize = i * n + j;
            assert(idx < vals.len());
            let v = vals[idx];
            row.push(v);
            j = j + 1;
        }
        mat.push(row);
        i = i + 1;
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

fn print_json(mat: &Vec<Vec<i32>>) {
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

fn gen_mode(rng: &mut Rng, mode: usize, idx: usize) -> (usize, Vec<i32>) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 100,
        4 => 99,
        5 => rng.gen_range_usize(1, 10),
        6 => rng.gen_range_usize(10, 50),
        7 => rng.gen_range_usize(50, 100),
        8 => if idx % 2 == 0 { 1 } else { 100 },
        9 => rng.gen_range_usize(1, 100),
        _ => rng.gen_range_usize(1, 100),
    };
    let size = n * n;
    let mut vals: Vec<i32> = Vec::with_capacity(size);
    match mode {
        0 | 1 | 2 => {
            for _ in 0..size {
                vals.push(rng.gen_range_i32(1, 100));
            }
        }
        3 | 4 => {
            let fill = rng.gen_range_i32(1, 100);
            for _ in 0..size {
                vals.push(fill);
            }
        }
        5 => {
            for _ in 0..size { vals.push(1); }
        }
        6 => {
            for _ in 0..size { vals.push(100); }
        }
        7 => {
            // alternating
            for k in 0..size {
                vals.push(if k % 2 == 0 { 1 } else { 100 });
            }
        }
        8 => {
            // diagonal heavy
            for i in 0..n {
                for j in 0..n {
                    if i == j || i + j == n - 1 {
                        vals.push(100);
                    } else {
                        vals.push(1);
                    }
                }
            }
        }
        _ => {
            for _ in 0..size {
                vals.push(rng.gen_range_i32(1, 100));
            }
        }
    }
    (n, vals)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 10usize;
    for t in 0..total {
        let mode = t % modes;
        let (n, vals) = gen_mode(&mut rng, mode, t);
        let mat = generate_test_case(n, &vals);
        print_json(&mat);
    }
}