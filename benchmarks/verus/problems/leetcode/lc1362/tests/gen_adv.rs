use vstd::prelude::*;

verus! {

pub fn generate_test_case(num: i32) -> (res: i32)
    requires
        1 <= num <= 1_000_000_000,
    ensures
        1 <= res <= 1_000_000_000,
{
    num
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn clamp_num(x: i64) -> i32 {
    let v = if x < 1 { 1 } else if x > 1_000_000_000 { 1_000_000_000 } else { x };
    v as i32
}

fn pick_num(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 1_000_000_000,
        2 => rng.gen_range_i32(1, 100),
        3 => rng.gen_range_i32(1, 10_000),
        4 => rng.gen_range_i32(1, 1_000_000_000),
        5 => {
            // near perfect squares: k*k - 1, k*k - 2
            let k = rng.gen_range_i32(2, 31622);
            let kk = (k as i64) * (k as i64);
            clamp_num(kk - 1)
        }
        6 => {
            let k = rng.gen_range_i32(2, 31622);
            let kk = (k as i64) * (k as i64);
            clamp_num(kk - 2)
        }
        7 => {
            // primes minus 1 / 2 => forces (1, num+1) or (1, num+2)
            let primes: [i32; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
            let p = primes[t % primes.len()] as i64;
            // make a large prime-ish: use 10^9 + 7 etc.
            let big_primes: [i64; 6] = [1_000_000_007, 999_999_937, 999_999_893, 100_000_007, 10_000_019, 1_000_003];
            let bp = big_primes[t % big_primes.len()];
            clamp_num(bp - 1 + (p % 3) - 1)
        }
        8 => {
            // num+1 = k*(k+1)
            let k = rng.gen_range_i32(2, 31622);
            let prod = (k as i64) * ((k + 1) as i64);
            clamp_num(prod - 1)
        }
        9 => {
            // powers of 2
            let e = rng.gen_range_i32(1, 29);
            let mut v: i64 = 1;
            for _ in 0..e { v *= 2; }
            clamp_num(v - 1)
        }
        _ => rng.gen_range_i32(1, 1_000_000_000),
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let num = pick_num(&mut rng, mode, t);
        let val = generate_test_case(num);
        println!("{{\"num\":{}}}", val);
    }
}