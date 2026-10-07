use vstd::prelude::*;

verus! {

pub fn generate_test_case(num: i32) -> (result: i32)
    requires
        10 <= num <= 1_000_000_000,
    ensures
        10 <= result <= 1_000_000_000,
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

fn clamp_num(n: i64) -> i32 {
    let mut v = n;
    if v < 10 {
        v = 10;
    }
    if v > 1_000_000_000 {
        v = 1_000_000_000;
    }
    v as i32
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => rng.gen_range_i32(10, 99),
        1 => rng.gen_range_i32(100, 999),
        2 => rng.gen_range_i32(1000, 9999),
        3 => rng.gen_range_i32(100000, 999999),
        4 => rng.gen_range_i32(10_000_000, 99_999_999),
        5 => rng.gen_range_i32(100_000_000, 999_999_999),
        6 => 1_000_000_000,
        7 => 10,
        8 => {
            // all same digit
            let d = rng.gen_range_i32(1, 9);
            let len = rng.gen_range_i32(2, 9) as usize;
            let mut v: i64 = 0;
            for _ in 0..len {
                v = v * 10 + d as i64;
            }
            clamp_num(v)
        }
        9 => {
            // has zeros
            let a = rng.gen_range_i32(1, 9);
            let len = rng.gen_range_i32(2, 9) as usize;
            let mut v: i64 = a as i64;
            for _ in 1..len {
                v = v * 10;
            }
            clamp_num(v)
        }
        10 => {
            // descending digits
            let len = rng.gen_range_i32(2, 9) as usize;
            let mut v: i64 = 0;
            let start = rng.gen_range_i32(1, 9);
            let mut d = start;
            for _ in 0..len {
                v = v * 10 + d as i64;
                if d > 0 { d -= 1; } else { d = 9; }
            }
            clamp_num(v)
        }
        _ => {
            let v = rng.gen_range_i32(10, 1_000_000_000);
            v
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
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let num = pick_for_mode(&mut rng, mode);
        let num = if num < 10 { 10 } else if num > 1_000_000_000 { 1_000_000_000 } else { num };
        let result = generate_test_case(num);
        println!("{{\"num\":{}}}", result);
    }
}