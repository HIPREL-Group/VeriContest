use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        10 <= n <= 1_000_000_000,
    ensures
        10 <= res <= 1_000_000_000,
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

fn clamp_n(x: i64) -> i32 {
    let mut v = x;
    if v < 10 { v = 10; }
    if v > 1_000_000_000 { v = 1_000_000_000; }
    v as i32
}

fn gen_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => {
            // small values near lower bound
            rng.gen_range_i32(10, 99)
        }
        1 => {
            // large values near upper bound
            rng.gen_range_i32(900_000_000, 1_000_000_000)
        }
        2 => {
            // all same digits
            let d = rng.gen_range_i32(1, 9);
            let len = rng.gen_range_i32(2, 9) as usize;
            let mut v: i64 = 0;
            for _ in 0..len {
                v = v * 10 + d as i64;
            }
            clamp_n(v)
        }
        3 => {
            // contains zeros
            let len = rng.gen_range_i32(2, 9) as usize;
            let mut v: i64 = rng.gen_range_i32(1, 9) as i64;
            for _ in 1..len {
                let d = if rng.next_u64() % 2 == 0 { 0 } else { rng.gen_range_i32(0, 9) as i64 };
                v = v * 10 + d;
            }
            clamp_n(v)
        }
        4 => {
            // nines dominant
            let len = rng.gen_range_i32(2, 9) as usize;
            let mut v: i64 = 0;
            for _ in 0..len {
                let d = if rng.next_u64() % 3 == 0 { rng.gen_range_i32(0, 9) as i64 } else { 9 };
                if v == 0 && d == 0 {
                    v = 9;
                } else {
                    v = v * 10 + d;
                }
            }
            clamp_n(v)
        }
        5 => {
            // exactly 2 digits
            rng.gen_range_i32(10, 99)
        }
        6 => {
            // boundary
            let choices = [10i32, 11, 99, 100, 1_000_000_000, 999_999_999, 123_456_789];
            choices[(t) % choices.len()]
        }
        7 => {
            // two distinct large digits only
            let d1 = rng.gen_range_i32(1, 9);
            let d2 = rng.gen_range_i32(0, 9);
            let len = rng.gen_range_i32(2, 9) as usize;
            let mut v: i64 = d1 as i64;
            for i in 1..len {
                let d = if i % 2 == 0 { d1 } else { d2 };
                v = v * 10 + d as i64;
            }
            clamp_n(v)
        }
        8 => {
            // random full-range
            let v = (rng.next_u64() % 999_999_991) as i64 + 10;
            clamp_n(v)
        }
        9 => {
            // single large digit then rest small
            let len = rng.gen_range_i32(2, 9) as usize;
            let mut v: i64 = 9;
            for _ in 1..len {
                v = v * 10 + rng.gen_range_i32(0, 3) as i64;
            }
            clamp_n(v)
        }
        _ => {
            let v = (rng.next_u64() % 999_999_991) as i64 + 10;
            clamp_n(v)
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
        let n = gen_for_mode(&mut rng, mode, t);
        let n = if n < 10 { 10 } else if n > 1_000_000_000 { 1_000_000_000 } else { n };
        let out = generate_test_case(n);
        println!("{{\"n\": {}}}", out);
    }
}