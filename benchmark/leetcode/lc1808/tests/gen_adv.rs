use vstd::prelude::*;

verus! {

pub fn generate_test_case(base_val: u64, exp_val: u64, modulus_val: u64) -> (result: (u64, u64, u64))
    requires
        modulus_val >= 1,
    ensures
        ({
            let (b, e, m) = result;
            b == base_val && e == exp_val && m == modulus_val && m >= 1
        }),
{
    (base_val, exp_val, modulus_val)
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

    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        if lo >= hi {
            return lo;
        }
        if lo == 0 && hi == u64::MAX {
            self.next_u64()
        } else {
            let span = hi - lo + 1;
            lo + (self.next_u64() % span)
        }
    }
}

fn pick_case(rng: &mut Rng, mode: usize) -> (u64, u64, u64) {
    match mode {
        0 => {
            // small values
            let b = rng.gen_range_u64(0, 20);
            let e = rng.gen_range_u64(0, 20);
            let m = rng.gen_range_u64(1, 100);
            (b, e, m)
        }
        1 => {
            // modulus = 1, result always 0
            let b = rng.gen_range_u64(0, u64::MAX / 2);
            let e = rng.gen_range_u64(0, u64::MAX / 2);
            (b, e, 1)
        }
        2 => {
            // exp = 0, result always 1 mod m (or 0 if m=1)
            let b = rng.gen_range_u64(0, u64::MAX / 2);
            let m = rng.gen_range_u64(1, 1_000_000_007);
            (b, 0, m)
        }
        3 => {
            // base = 0
            let e = rng.gen_range_u64(0, 1000);
            let m = rng.gen_range_u64(1, 1_000_000_007);
            (0, e, m)
        }
        4 => {
            // base = 1
            let e = rng.gen_range_u64(0, u64::MAX / 2);
            let m = rng.gen_range_u64(1, 1_000_000_007);
            (1, e, m)
        }
        5 => {
            // common prime modulus
            let b = rng.gen_range_u64(0, 2_000_000_000);
            let e = rng.gen_range_u64(0, 1_000_000_000);
            (b, e, 1_000_000_007)
        }
        6 => {
            // large base, large exp
            let b = rng.gen_range_u64(1_000_000_000, u64::MAX / 2);
            let e = rng.gen_range_u64(1_000_000_000, u64::MAX / 2);
            let m = rng.gen_range_u64(2, 1_000_000_007);
            (b, e, m)
        }
        7 => {
            // large modulus (edge of u64)
            let b = rng.gen_range_u64(0, u64::MAX);
            let e = rng.gen_range_u64(0, 64);
            let m = rng.gen_range_u64(u64::MAX / 2, u64::MAX);
            (b, e, m)
        }
        8 => {
            // exp = 1
            let b = rng.gen_range_u64(0, u64::MAX / 2);
            let m = rng.gen_range_u64(1, u64::MAX / 2);
            (b, 1, m)
        }
        9 => {
            // power-of-two moduli
            let b = rng.gen_range_u64(0, u64::MAX / 2);
            let e = rng.gen_range_u64(0, 100);
            let shift = rng.gen_range_u64(1, 62);
            let m = 1u64 << shift;
            (b, e, m)
        }
        10 => {
            // base just under modulus
            let m = rng.gen_range_u64(2, 1_000_000_000);
            let b = if m > 0 { m - 1 } else { 0 };
            let e = rng.gen_range_u64(0, 1_000_000);
            (b, e, m)
        }
        _ => {
            let b = rng.gen_range_u64(0, u64::MAX);
            let e = rng.gen_range_u64(0, u64::MAX);
            let m = rng.gen_range_u64(1, u64::MAX);
            (b, e, m)
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
        let (b, e, m) = pick_case(&mut rng, mode);
        let (bb, ee, mm) = generate_test_case(b, e, m);
        // reference_oracle expects "prime_factors" (i32) for Solution::max_nice_divisors.
        let _ = (ee, mm);
        let pf = ((bb % 1_000_000_000) + 1) as i32;
        println!("{{\"prime_factors\":{}}}", pf);
    }
}
