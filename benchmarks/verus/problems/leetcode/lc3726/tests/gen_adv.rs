use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i64) -> (n: i64)
    requires
        1 <= n_val <= 1_000_000_000_000_000,
    ensures
        1 <= n <= 1_000_000_000_000_000,
{
    n_val
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i64 {
    match mode {
        0 => 1,
        1 => 1_000_000_000_000_000,
        2 => {
            // all zeros after first digit
            let digits = rng.gen_range_i64(1, 15) as u32;
            let mut v: i64 = rng.gen_range_i64(1, 9);
            for _ in 0..digits {
                v = v * 10;
            }
            if v > 1_000_000_000_000_000 { 1_000_000_000_000_000 } else { v }
        }
        3 => {
            // no zeros
            let digits = rng.gen_range_i64(1, 15) as u32;
            let mut v: i64 = 0;
            for _ in 0..digits {
                let d = rng.gen_range_i64(1, 9);
                v = v * 10 + d;
            }
            if v < 1 { 1 } else { v }
        }
        4 => {
            // many zeros interspersed
            let digits = rng.gen_range_i64(2, 15) as u32;
            let mut v: i64 = rng.gen_range_i64(1, 9);
            for _ in 1..digits {
                let d = if rng.next_u64() % 2 == 0 { 0 } else { rng.gen_range_i64(1, 9) };
                v = v * 10 + d;
            }
            if v < 1 { 1 } else if v > 1_000_000_000_000_000 { 1_000_000_000_000_000 } else { v }
        }
        5 => {
            // trailing zeros
            let mut v: i64 = rng.gen_range_i64(1, 999_999);
            let zeros = rng.gen_range_i64(0, 9) as u32;
            for _ in 0..zeros {
                if v <= 100_000_000_000_000 {
                    v = v * 10;
                }
            }
            v
        }
        6 => {
            // leading-after-first zero: like 10000...1
            let d = rng.gen_range_i64(1, 9);
            let zeros = rng.gen_range_i64(1, 13) as u32;
            let mut v: i64 = d;
            for _ in 0..zeros {
                v = v * 10;
            }
            v = v + rng.gen_range_i64(1, 9);
            if v > 1_000_000_000_000_000 { 1_000_000_000_000_000 } else { v }
        }
        7 => 10,
        8 => 100,
        9 => 1020030,
        _ => rng.gen_range_i64(1, 1_000_000_000_000_000),
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
        let mut v = pick_for_mode(&mut rng, mode);
        if v < 1 {
            v = 1;
        }
        if v > 1_000_000_000_000_000 {
            v = 1_000_000_000_000_000;
        }
        let n = generate_test_case(v);
        println!("{{\"n\":{}}}", n);
    }
}