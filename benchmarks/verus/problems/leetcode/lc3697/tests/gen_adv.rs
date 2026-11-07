use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 1_000_000_000,
    ensures
        1 <= result <= 1_000_000_000,
        result == n,
{
    n
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn adversarial(mode: usize, rng: &mut Rng) -> i32 {
    match mode {
        0 => 1,
        1 => 1_000_000_000,
        2 => 9,
        3 => 10,
        4 => 100,
        5 => {
            // single-digit
            rng.gen_range_i32(1, 9)
        }
        6 => {
            // pure powers of 10
            let powers = [1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000];
            powers[(rng.next_u64() as usize) % powers.len()]
        }
        7 => {
            // 537 style - many nonzero digits
            let digits = (rng.next_u64() % 9) + 1;
            let mut v: i64 = 0;
            for _ in 0..digits {
                let d = (rng.next_u64() % 9) + 1;
                v = v * 10 + d as i64;
            }
            if v > 1_000_000_000 { 1_000_000_000 } else { v as i32 }
        }
        8 => {
            // numbers with many zeros
            let d = (rng.next_u64() % 9) + 1;
            let zeros = (rng.next_u64() % 9) as u32;
            let mut v: i64 = d as i64;
            for _ in 0..zeros {
                v *= 10;
            }
            if v > 1_000_000_000 { 1_000_000_000 } else { v as i32 }
        }
        9 => {
            // small numbers
            rng.gen_range_i32(1, 100)
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = adversarial(mode, &mut rng);
        let n = if n < 1 { 1 } else if n > 1_000_000_000 { 1_000_000_000 } else { n };
        let result = generate_test_case(n);
        println!("{{\"n\":{}}}", result);
    }
}