use vstd::prelude::*;

verus! {

pub fn generate_test_case(num: i32) -> (res: i32)
    requires
        0 <= num <= 1_000_000,
    ensures
        0 <= res <= 1_000_000,
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 1_000_000,
        3 => 999_999,
        4 => {
            // ending with trailing zeros
            let base = rng.gen_range_i32(1, 1000);
            let mul = match rng.next_u64() % 4 { 0 => 10, 1 => 100, 2 => 1000, _ => 10000 };
            let v = base * mul;
            if v > 1_000_000 { 1_000_000 } else { v }
        }
        5 => {
            // palindromes
            let d = rng.gen_range_i32(0, 9);
            d * 111111 % 1_000_001
        }
        6 => {
            // random small
            rng.gen_range_i32(0, 100)
        }
        7 => {
            // random full-range
            rng.gen_range_i32(0, 1_000_000)
        }
        8 => {
            // powers of 10
            let p = rng.next_u64() % 7;
            let mut v: i32 = 1;
            for _ in 0..p { v *= 10; }
            v
        }
        9 => {
            // numbers with internal zeros
            let a = rng.gen_range_i32(1, 9);
            let b = rng.gen_range_i32(1, 9);
            a * 1000 + b
        }
        _ => rng.gen_range_i32(0, 1_000_000),
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
        let mut num = pick_for_mode(&mut rng, mode);
        if num < 0 { num = 0; }
        if num > 1_000_000 { num = 1_000_000; }
        let out = generate_test_case(num);
        println!("{{\"num\":{}}}", out);
    }
}