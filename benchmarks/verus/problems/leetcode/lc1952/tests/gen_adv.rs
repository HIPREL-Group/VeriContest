use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1 <= n <= 10_000,
    ensures
        1 <= res <= 10_000,
{
    n
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

fn pick_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 4,
        2 => 2,
        3 => {
            // perfect squares of primes -> should be true
            let primes = [2i32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97];
            let p = primes[t % primes.len()];
            p * p
        }
        4 => {
            // primes -> false (2 divisors)
            let primes = [2i32, 3, 5, 7, 11, 13, 97, 101, 9973, 9967];
            primes[t % primes.len()]
        }
        5 => {
            // perfect squares that are NOT prime squares -> false
            let vals = [16i32, 36, 64, 81, 100, 144, 196, 225, 256, 324, 400, 625, 900, 1296, 2401, 10000];
            vals[t % vals.len()]
        }
        6 => 10_000,
        7 => {
            // small values 1..20
            1 + (t as i32 % 20)
        }
        8 => {
            // random
            rng.gen_range_i32(1, 10_000)
        }
        9 => {
            // p^3 -> 4 divisors, not 3
            let vals = [8i32, 27, 125, 343, 1331, 2197];
            vals[t % vals.len()]
        }
        _ => rng.gen_range_i32(1, 10_000),
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
        let n = pick_for_mode(&mut rng, mode, t);
        let n = if n < 1 { 1 } else if n > 10_000 { 10_000 } else { n };
        let v = generate_test_case(n);
        println!("{{\"n\":{}}}", v);
    }
}