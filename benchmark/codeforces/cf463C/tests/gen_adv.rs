use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    flat: &Vec<i64>,
) -> (result: (usize, Vec<i64>))
    requires
        2 <= n <= 2000,
        flat.len() == n * n,
        forall |k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 1_000_000_000,
    ensures
        result.0 == n,
        2 <= result.0 <= 2000,
        result.1.len() == result.0 * result.0,
        2 <= result.1.len(),
        result.1.len() <= 4_000_000,
        forall |k: int| 0 <= k < result.1.len() ==> 0 <= #[trigger] result.1[k] <= 1_000_000_000,
{
    let mut board: Vec<i64> = Vec::new();
    let total: usize = n * n;
    let mut i: usize = 0;

    assert(n >= 2);
    assert(n <= 2000);
    assert(total == n * n);
    assert(total <= 2000 * 2000) by (nonlinear_arith) requires n <= 2000, total == n * n;
    assert(total >= 4) by (nonlinear_arith) requires n >= 2, total == n * n;

    while i < total
        invariant
            total == n * n,
            2 <= n <= 2000,
            flat.len() == total,
            0 <= i <= total,
            board.len() == i,
            forall |k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < board.len() ==> 0 <= #[trigger] board[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < board.len() ==> board[k] == flat[k],
        decreases total - i,
    {
        board.push(flat[i]);
        i = i + 1;
    }

    (n, board)
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn build_flat(n: usize, values: Vec<i64>) -> Vec<i64> {
    let total = n * n;
    let mut out = Vec::with_capacity(total);
    for i in 0..total {
        let v = values[i % values.len()];
        let vc = if v < 0 { 0 } else if v > 1_000_000_000 { 1_000_000_000 } else { v };
        out.push(vc);
    }
    out
}

fn make_board(rng: &mut Rng, n: usize, mode: usize) -> Vec<i64> {
    let total = n * n;
    let mut v: Vec<i64> = Vec::with_capacity(total);
    match mode {
        0 => {
            // all zeros
            for _ in 0..total { v.push(0); }
        }
        1 => {
            // all max
            for _ in 0..total { v.push(1_000_000_000); }
        }
        2 => {
            // random small
            for _ in 0..total { v.push(rng.gen_range_i64(0, 10)); }
        }
        3 => {
            // random full range
            for _ in 0..total { v.push(rng.gen_range_i64(0, 1_000_000_000)); }
        }
        4 => {
            // mostly zero with a few large
            for _ in 0..total { v.push(0); }
            let spikes = 5.min(total);
            for _ in 0..spikes {
                let idx = rng.gen_range_usize(0, total - 1);
                v[idx] = 1_000_000_000;
            }
        }
        5 => {
            // checkerboard pattern
            for i in 0..n {
                for j in 0..n {
                    if (i + j) % 2 == 0 {
                        v.push(1_000_000_000);
                    } else {
                        v.push(0);
                    }
                }
            }
        }
        6 => {
            // diagonal heavy
            for i in 0..n {
                for j in 0..n {
                    if i == j || i + j == n - 1 {
                        v.push(rng.gen_range_i64(500_000_000, 1_000_000_000));
                    } else {
                        v.push(rng.gen_range_i64(0, 100));
                    }
                }
            }
        }
        7 => {
            // one big cell
            for _ in 0..total { v.push(0); }
            let idx = rng.gen_range_usize(0, total - 1);
            v[idx] = 1_000_000_000;
        }
        8 => {
            // row-gradient
            for i in 0..n {
                for _j in 0..n {
                    v.push((i as i64) * 1000);
                }
            }
        }
        9 => {
            // col-gradient
            for _i in 0..n {
                for j in 0..n {
                    v.push((j as i64) * 1000);
                }
            }
        }
        _ => {
            for _ in 0..total { v.push(rng.gen_range_i64(0, 1_000_000_000)); }
        }
    }
    // safety clamp
    for x in v.iter_mut() {
        if *x < 0 { *x = 0; }
        if *x > 1_000_000_000 { *x = 1_000_000_000; }
    }
    v
}

fn print_json(n: usize, board: &[i64]) {
    // board as 2D array of length n arrays of length n
    print!("{{\"n\":{},\"board\":[", n);
    for i in 0..n {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..n {
            if j > 0 { print!(","); }
            print!("{}", board[i * n + j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total_cases = 200usize;

    for t in 0..total_cases {
        let mode = t % modes;
        let n: usize = match t % 13 {
            0 => 2,
            1 => 3,
            2 => 4,
            3 => 5,
            4 => 8,
            5 => 16,
            6 => 32,
            7 => 50,
            8 => 100,
            9 => 200,
            10 => 500,
            11 => 1000,
            _ => 2 + (t % 20),
        };
        let n = if n < 2 { 2 } else if n > 2000 { 2000 } else { n };
        // keep output manageable: cap n for large cases
        let n = if n > 200 { 200 } else { n };

        let board = make_board(&mut rng, n, mode);
        let flat = build_flat(n, board);
        let (nn, bb) = generate_test_case(n, &flat);
        print_json(nn, &bb);
    }
}