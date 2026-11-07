use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, k: i32) -> (result: (i32, i32))
    requires
        1 <= n <= 1_000_000,
        1 <= k <= 1_000_000,
    ensures
        1 <= result.0 <= 1_000_000,
        1 <= result.1 <= 1_000_000,
{
    (n, k)
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
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => {
            // equal
            let x = rng.gen_range_i32(1, 1_000_000);
            (x, x)
        }
        1 => {
            // small values
            let a = rng.gen_range_i32(1, 20);
            let b = rng.gen_range_i32(1, 20);
            (a, b)
        }
        2 => {
            // k is submask of n by construction: set n=k|extra
            let k = rng.gen_range_i32(1, 1_000_000);
            let extra = rng.gen_range_i32(0, 1_000_000);
            let n_val = k | extra;
            let n_clamped = if n_val < 1 { 1 } else if n_val > 1_000_000 { 1_000_000 } else { n_val };
            let k_clamped = if k > n_clamped { n_clamped } else { k };
            (n_clamped, k_clamped)
        }
        3 => {
            // k has bit not in n (likely impossible)
            let n_val = rng.gen_range_i32(1, 1_000_000);
            let k_val = rng.gen_range_i32(1, 1_000_000);
            (n_val, k_val)
        }
        4 => {
            // boundary: n=1, k=1
            (1, 1)
        }
        5 => {
            // max values
            (1_000_000, 1_000_000)
        }
        6 => {
            // n=max, k=1
            (1_000_000, 1)
        }
        7 => {
            // powers of 2
            let p = rng.gen_range_i32(0, 19);
            let q = rng.gen_range_i32(0, 19);
            let mut a: i32 = 1;
            for _ in 0..p { if a < 500_000 { a *= 2; } }
            let mut b: i32 = 1;
            for _ in 0..q { if b < 500_000 { b *= 2; } }
            (a, b)
        }
        8 => {
            // n = 2^k - 1 (all ones), k = random
            let bits = rng.gen_range_i32(1, 19);
            let mut n_val: i32 = 1;
            for _ in 1..bits { n_val = n_val * 2 + 1; }
            if n_val > 1_000_000 { n_val = 1_000_000; }
            let k_val = rng.gen_range_i32(1, n_val);
            (n_val, k_val)
        }
        9 => {
            // k=n-1
            let n_val = rng.gen_range_i32(2, 1_000_000);
            (n_val, n_val - 1)
        }
        _ => {
            let n_val = rng.gen_range_i32(1, 1_000_000);
            let k_val = rng.gen_range_i32(1, 1_000_000);
            (n_val, k_val)
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, k) = pick_case(&mut rng, mode);
        let n_clamped = if n < 1 { 1 } else if n > 1_000_000 { 1_000_000 } else { n };
        let k_clamped = if k < 1 { 1 } else if k > 1_000_000 { 1_000_000 } else { k };
        let (nn, kk) = generate_test_case(n_clamped, k_clamped);
        println!("{{\"n\":{},\"k\":{}}}", nn, kk);
    }
}