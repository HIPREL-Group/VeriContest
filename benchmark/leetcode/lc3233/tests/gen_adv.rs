use vstd::prelude::*;

verus! {

pub fn generate_test_case(l_val: i32, r_val: i32) -> (result: (i32, i32))
    requires
        1 <= l_val <= r_val <= 1000000000,
    ensures
        1 <= result.0 <= result.1 <= 1000000000,
{
    (l_val, r_val)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => {
            // small range
            let l = rng.gen_range_i32(1, 20);
            let r = rng.gen_range_i32(l, 20);
            (l, r)
        }
        1 => {
            // l == r
            let l = rng.gen_range_i32(1, 1_000_000_000);
            (l, l)
        }
        2 => {
            // l == 1
            let r = rng.gen_range_i32(1, 1_000_000_000);
            (1, r)
        }
        3 => {
            // r == 10^9
            let l = rng.gen_range_i32(1, 1_000_000_000);
            (l, 1_000_000_000)
        }
        4 => {
            // full range
            (1, 1_000_000_000)
        }
        5 => {
            // small l, small r (containing squares of primes)
            let l = rng.gen_range_i32(1, 100);
            let r = rng.gen_range_i32(l, 100);
            (l, r)
        }
        6 => {
            // around squares of primes
            let primes = [2i32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
            let idx = (rng.next_u64() as usize) % primes.len();
            let p = primes[idx];
            let sq = p * p;
            let lo = (sq - 2).max(1);
            let hi = (sq + 2).min(1_000_000_000);
            (lo, hi)
        }
        7 => {
            // medium range
            let l = rng.gen_range_i32(1, 1_000_000);
            let r = rng.gen_range_i32(l, (l as i64 + 1_000_000).min(1_000_000_000) as i32);
            (l, r)
        }
        8 => {
            // large l, large r
            let l = rng.gen_range_i32(999_000_000, 1_000_000_000);
            let r = rng.gen_range_i32(l, 1_000_000_000);
            (l, r)
        }
        9 => {
            // near large prime square: 31607^2 = 999402449
            let sq = 999_402_449;
            let lo = (sq - 5).max(1);
            let hi = (sq + 5).min(1_000_000_000);
            (lo, hi)
        }
        _ => {
            let l = rng.gen_range_i32(1, 1_000_000_000);
            let r = rng.gen_range_i32(l, 1_000_000_000);
            (l, r)
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
        let (l, r) = pick_for_mode(&mut rng, mode);
        let (lv, rv) = generate_test_case(l, r);
        println!("{{\"l\": {}, \"r\": {}}}", lv, rv);
    }
}