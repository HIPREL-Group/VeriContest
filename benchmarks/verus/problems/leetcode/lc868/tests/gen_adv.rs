use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 1_000_000_000,
    ensures
        1 <= result <= 1_000_000_000,
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 1_000_000_000,
        2 => 2,
        3 => {
            // Powers of 2 (single bit) -> gap = 0
            let k = rng.gen_range_i32(0, 29) as u32;
            (1i32 << k).max(1)
        }
        4 => {
            // 2^k + 1 -> two ones at extremes
            let k = rng.gen_range_i32(1, 29) as u32;
            (1i32 << k) + 1
        }
        5 => {
            // Alternating bits 0101...
            let k = rng.gen_range_i32(1, 15);
            let mut v: i32 = 0;
            for i in 0..k {
                v |= 1i32 << (2 * i);
            }
            v.max(1)
        }
        6 => {
            // All ones up to k bits
            let k = rng.gen_range_i32(1, 29);
            let mut v: i32 = 0;
            for i in 0..k {
                v |= 1i32 << i;
            }
            v.max(1)
        }
        7 => {
            // Two adjacent bits far apart
            let k = rng.gen_range_i32(2, 29) as u32;
            (1i32 << k) | 1
        }
        8 => {
            // Random small
            rng.gen_range_i32(1, 1000)
        }
        9 => {
            // Random large
            rng.gen_range_i32(1, 1_000_000_000)
        }
        _ => {
            rng.gen_range_i32(1, 1_000_000_000)
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
    let modes = 10usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let mut n = pick_for_mode(&mut rng, mode);
        if n < 1 {
            n = 1;
        }
        if n > 1_000_000_000 {
            n = 1_000_000_000;
        }
        let v = generate_test_case(n);
        println!("{{\"n\":{}}}", v);
    }
}