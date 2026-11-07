use vstd::prelude::*;

verus! {

pub fn generate_test_case(m: i32, n: i32, k: i32) -> (result: (i32, i32, i32))
    ensures
        ({
            let (mm, nn, kk) = result;
            &&& 1 <= mm <= 30000
            &&& 1 <= nn <= 30000
            &&& 1 <= kk
            &&& kk as int <= mm as int * nn as int
        }),
{
    let m = if m < 1 { 1 } else if m > 30000 { 30000 } else { m };
    let n = if n < 1 { 1 } else if n > 30000 { 30000 } else { n };
    assert(1 <= m * n <= 900000000) by(nonlinear_arith)
        requires 1 <= m <= 30000, 1 <= n <= 30000;
    let limit = m * n;
    let k = if k < 1 { 1 } else if k > limit { limit } else { k };
    (m, n, k)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn clamp_k(m: i32, n: i32, k: i64) -> i32 {
    let maxk = m as i64 * n as i64;
    let mut r = k;
    if r < 1 { r = 1; }
    if r > maxk { r = maxk; }
    r as i32
}

fn pick_case(rng: &mut Rng, mode: usize, t: usize) -> (i32, i32, i32) {
    match mode {
        0 => {
            // tiny
            let m = rng.gen_range_i32(1, 5);
            let n = rng.gen_range_i32(1, 5);
            let maxk = m as i64 * n as i64;
            let k = rng.gen_range_i32(1, maxk as i32);
            (m, n, k)
        }
        1 => {
            // m=1
            let m = 1;
            let n = rng.gen_range_i32(1, 30000);
            let k = rng.gen_range_i32(1, n);
            (m, n, k)
        }
        2 => {
            // n=1
            let n = 1;
            let m = rng.gen_range_i32(1, 30000);
            let k = rng.gen_range_i32(1, m);
            (m, n, k)
        }
        3 => {
            // max size, k=1
            (30000, 30000, 1)
        }
        4 => {
            // max size, k=max
            (30000, 30000, 900000000)
        }
        5 => {
            // max size, k middle
            let m = 30000i64;
            let n = 30000i64;
            let maxk = m * n;
            let k = clamp_k(30000, 30000, maxk / 2);
            (30000, 30000, k)
        }
        6 => {
            // square
            let s = rng.gen_range_i32(2, 1000);
            let maxk = s as i64 * s as i64;
            let k = clamp_k(s, s, rng.next_u64() as i64 % maxk + 1);
            (s, s, k)
        }
        7 => {
            // k=1
            let m = rng.gen_range_i32(1, 30000);
            let n = rng.gen_range_i32(1, 30000);
            (m, n, 1)
        }
        8 => {
            // k=max
            let m = rng.gen_range_i32(1, 30000);
            let n = rng.gen_range_i32(1, 30000);
            let maxk = m as i64 * n as i64;
            (m, n, clamp_k(m, n, maxk))
        }
        9 => {
            // skewed m >> n
            let m = rng.gen_range_i32(1000, 30000);
            let n = rng.gen_range_i32(1, 10);
            let maxk = m as i64 * n as i64;
            let k = clamp_k(m, n, (rng.next_u64() % (maxk as u64)) as i64 + 1);
            (m, n, k)
        }
        _ => {
            // random general
            let m = rng.gen_range_i32(1, 30000);
            let n = rng.gen_range_i32(1, 30000);
            let maxk = m as i64 * n as i64;
            let kraw = (rng.next_u64() as i64).rem_euclid(maxk) + 1;
            let k = clamp_k(m, n, kraw);
            let _ = t;
            (m, n, k)
        }
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
        let (m, n, k) = pick_case(&mut rng, mode, t);
        let (mm, nn, kk) = generate_test_case(m, n, k);
        println!("{{\"m\": {}, \"n\": {}, \"k\": {}}}", mm, nn, kk);
    }
}
