use vstd::prelude::*;

verus! {

pub open spec fn spec_first_mult2(l: int, k: int) -> int {
    (l + k - 1) / k * k
}

pub fn generate_test_case(n: usize, l: i32, r: i32) -> (res: (usize, i32, i32))
    requires
        1 <= n <= 100_000,
        1 <= l <= r <= 1_000_000_000,
    ensures
        res.0 == n,
        res.1 == l,
        res.2 == r,
        1 <= res.0 <= 100_000,
        1 <= res.1 <= res.2 <= 1_000_000_000,
{
    (n, l, r)
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn pick_case(rng: &mut Rng, mode: usize) -> (usize, i32, i32) {
    match mode {
        0 => {
            // n=1, simple
            let l = rng.gen_range_i64(1, 1_000_000_000) as i32;
            let r = rng.gen_range_i64(l as i64, 1_000_000_000) as i32;
            (1, l, r)
        }
        1 => {
            // small n, small l,r
            let n = rng.gen_range_usize(1, 10);
            let l = rng.gen_range_i64(1, 20) as i32;
            let r = rng.gen_range_i64(l as i64, 30) as i32;
            (n, l, r)
        }
        2 => {
            // l == r
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i64(1, 1_000_000_000) as i32;
            (n, v, v)
        }
        3 => {
            // Maximum n
            let l = rng.gen_range_i64(1, 500_000_000) as i32;
            let r = rng.gen_range_i64(l as i64, 1_000_000_000) as i32;
            (100_000, l, r)
        }
        4 => {
            // l=1, r=1
            (rng.gen_range_usize(1, 100_000), 1, 1)
        }
        5 => {
            // Boundary: r = 10^9
            let n = rng.gen_range_usize(1, 100_000);
            let l = rng.gen_range_i64(1, 1_000_000_000) as i32;
            (n, l, 1_000_000_000)
        }
        6 => {
            // r - l small
            let n = rng.gen_range_usize(1, 1000);
            let l = rng.gen_range_i64(1, 999_999_990) as i32;
            let diff = rng.gen_range_i64(0, 10) as i32;
            (n, l, l + diff)
        }
        7 => {
            // Large n, narrow range - likely NO
            let n = rng.gen_range_usize(50_000, 100_000);
            let l = rng.gen_range_i64(1, 999_000_000) as i32;
            let r = l + rng.gen_range_i64(0, 1000) as i32;
            (n, l, r)
        }
        8 => {
            // Tiny l, large r
            let n = rng.gen_range_usize(1, 100_000);
            (n, 1, 1_000_000_000)
        }
        9 => {
            // l=r=1_000_000_000
            let n = rng.gen_range_usize(1, 100_000);
            (n, 1_000_000_000, 1_000_000_000)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100_000);
            let l = rng.gen_range_i64(1, 1_000_000_000) as i32;
            let r = rng.gen_range_i64(l as i64, 1_000_000_000) as i32;
            (n, l, r)
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
        let (n, l, r) = pick_case(&mut rng, mode);
        let (n2, l2, r2) = generate_test_case(n, l, r);
        println!("{{\"n\": {}, \"l\": {}, \"r\": {}}}", n2, l2, r2);
    }
}