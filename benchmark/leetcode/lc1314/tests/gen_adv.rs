use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    k: i32,
    fill_val: i32,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= m <= 100,
        1 <= n <= 100,
        1 <= k <= 100,
        1 <= fill_val <= 100,
    ensures
        ({
            let mat = result.0;
            let kk = result.1;
            &&& 1 <= mat.len() <= 100
            &&& 1 <= mat[0].len() <= 100
            &&& forall |i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len()
            &&& forall |i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==>
                1 <= #[trigger] mat[i][j] <= 100
            &&& 1 <= kk <= 100
        }),
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            1 <= m <= 100,
            1 <= n <= 100,
            1 <= fill_val <= 100,
            0 <= i <= m,
            mat.len() == i,
            forall |a: int| 0 <= a < mat.len() ==> #[trigger] mat[a].len() == n,
            forall |a: int, b: int| 0 <= a < mat.len() && 0 <= b < n ==>
                1 <= #[trigger] mat[a][b] <= 100,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 100,
                1 <= fill_val <= 100,
                0 <= j <= n,
                row.len() == j,
                forall |b: int| 0 <= b < row.len() ==> 1 <= #[trigger] row[b] <= 100,
            decreases n - j,
        {
            row.push(fill_val);
            j = j + 1;
        }
        mat.push(row);
        i = i + 1;
    }

    assert(mat.len() == m);
    assert(mat[0].len() == n);

    (mat, k)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn print_json(mat: &Vec<Vec<i32>>, k: i32) {
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
    println!("],\"k\":{}}}", k);
}

fn pick_params(rng: &mut Rng, mode: usize) -> (usize, usize, i32, i32) {
    match mode {
        0 => (1, 1, 1, 1),
        1 => (1, 1, 100, 100),
        2 => (100, 100, 1, 1),
        3 => (100, 100, 100, 100),
        4 => (100, 100, 50, 50),
        5 => (1, 100, rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100)),
        6 => (100, 1, rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100)),
        7 => (rng.gen_range_usize(1, 10), rng.gen_range_usize(1, 10), 1, rng.gen_range_i32(1, 100)),
        8 => (rng.gen_range_usize(1, 10), rng.gen_range_usize(1, 10), 100, rng.gen_range_i32(1, 100)),
        9 => (3, 3, 1, rng.gen_range_i32(1, 100)),
        _ => (
            rng.gen_range_usize(1, 100),
            rng.gen_range_usize(1, 100),
            rng.gen_range_i32(1, 100),
            rng.gen_range_i32(1, 100),
        ),
    }
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
        let (m, n, k, fill) = pick_params(&mut rng, mode);
        let (mat, kk) = generate_test_case(m, n, k, fill);
        print_json(&mat, kk);
    }
}