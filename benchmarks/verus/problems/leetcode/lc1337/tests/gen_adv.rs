use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    k: i32,
    bits: &Vec<Vec<i32>>,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        2 <= m <= 100,
        2 <= n <= 100,
        1 <= k <= m as i32,
        bits.len() == m,
        forall |i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]).len() == n,
        forall |i: int, j: int| 0 <= i < bits.len() && 0 <= j < bits[i].len()
            ==> #[trigger] bits[i][j] == 0 || bits[i][j] == 1,
    ensures
        2 <= result.0.len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 2 <= (#[trigger] result.0[i]).len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0[i]).len() == result.0[0].len(),
        1 <= result.1 <= result.0.len() as i32,
        forall |i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len()
            ==> #[trigger] result.0[i][j] == 0 || result.0[i][j] == 1,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i <= m,
            2 <= m <= 100,
            2 <= n <= 100,
            bits.len() == m,
            mat.len() == i,
            forall |p: int| 0 <= p < bits.len() ==> (#[trigger] bits[p]).len() == n,
            forall |p: int, q: int| 0 <= p < bits.len() && 0 <= q < bits[p].len()
                ==> #[trigger] bits[p][q] == 0 || bits[p][q] == 1,
            forall |p: int| 0 <= p < mat.len() ==> (#[trigger] mat[p]).len() == n,
            forall |p: int, q: int| 0 <= p < mat.len() && 0 <= q < mat[p].len()
                ==> #[trigger] mat[p][q] == 0 || mat[p][q] == 1,
        decreases m - i,
    {
        let row = &bits[i];
        let mut new_row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                2 <= n <= 100,
                row.len() == n,
                new_row.len() == j,
                forall |q: int| 0 <= q < row.len() ==> #[trigger] row[q] == 0 || row[q] == 1,
                forall |q: int| 0 <= q < new_row.len() ==> #[trigger] new_row[q] == row[q],
                forall |q: int| 0 <= q < new_row.len() ==> #[trigger] new_row[q] == 0 || new_row[q] == 1,
            decreases n - j,
        {
            new_row.push(row[j]);
            j = j + 1;
        }
        mat.push(new_row);
        i = i + 1;
    }

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
}

fn make_row_with_soldiers(n: usize, s: usize) -> Vec<i32> {
    let mut row = Vec::with_capacity(n);
    let cap = if s > n { n } else { s };
    for i in 0..n {
        if i < cap {
            row.push(1);
        } else {
            row.push(0);
        }
    }
    row
}

fn make_random_row(rng: &mut Rng, n: usize) -> Vec<i32> {
    let s = rng.gen_range_usize(0, n);
    make_row_with_soldiers(n, s)
}

fn build_bits(rng: &mut Rng, mode: usize, m: usize, n: usize) -> Vec<Vec<i32>> {
    let mut bits: Vec<Vec<i32>> = Vec::new();
    match mode {
        0 => {
            for _ in 0..m {
                bits.push(make_random_row(rng, n));
            }
        }
        1 => {
            for _ in 0..m {
                bits.push(make_row_with_soldiers(n, 0));
            }
        }
        2 => {
            for _ in 0..m {
                bits.push(make_row_with_soldiers(n, n));
            }
        }
        3 => {
            for i in 0..m {
                let s = (i * n) / m;
                bits.push(make_row_with_soldiers(n, s));
            }
        }
        4 => {
            for i in 0..m {
                let s = n - ((i * n) / m);
                bits.push(make_row_with_soldiers(n, s));
            }
        }
        5 => {
            let s = rng.gen_range_usize(0, n);
            for _ in 0..m {
                bits.push(make_row_with_soldiers(n, s));
            }
        }
        6 => {
            for i in 0..m {
                let s = if i % 2 == 0 { 0 } else { n };
                bits.push(make_row_with_soldiers(n, s));
            }
        }
        7 => {
            for _ in 0..m {
                let s = if rng.next_u64() % 2 == 0 { 0 } else { n };
                bits.push(make_row_with_soldiers(n, s));
            }
        }
        8 => {
            for i in 0..m {
                let s = if i < m / 2 { 1 } else { 2 };
                bits.push(make_row_with_soldiers(n, s.min(n)));
            }
        }
        9 => {
            for _ in 0..m {
                let choices = [0usize, 1, n / 2, n - 1, n];
                let idx = (rng.next_u64() as usize) % choices.len();
                let s = choices[idx].min(n);
                bits.push(make_row_with_soldiers(n, s));
            }
        }
        _ => {
            for _ in 0..m {
                bits.push(make_random_row(rng, n));
            }
        }
    }
    bits
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
        let m = match mode {
            1 => 100,
            2 => 2,
            3 => 50,
            4 => 100,
            5 => 10,
            _ => rng.gen_range_usize(2, 100),
        };
        let n = match mode {
            1 => 100,
            2 => 2,
            3 => rng.gen_range_usize(2, 100),
            _ => rng.gen_range_usize(2, 100),
        };
        let k = rng.gen_range_usize(1, m) as i32;
        let bits = build_bits(&mut rng, mode, m, n);
        let (mat, kk) = generate_test_case(m, n, k, &bits);
        print_json(&mat, kk);
    }
}