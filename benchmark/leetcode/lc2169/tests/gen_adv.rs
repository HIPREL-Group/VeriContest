use vstd::prelude::*;

verus! {

pub fn generate_test_case(num1: i32, num2: i32) -> (result: (i32, i32))
    ensures
        0 <= result.0 && 0 <= result.1,
        result.0 as int + result.1 as int <= 200_000,
        result.0 <= 100_000,
        result.1 <= 100_000,
{
    let num1 = if num1 < 0 { 0 } else if num1 > 100000 { 100000 } else { num1 };
    let num2 = if num2 < 0 { 0 } else if num2 > 100000 { 100000 } else { num2 };
    (num1, num2)
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
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (0, 0),
        1 => (0, rng.gen_range_i32(0, 100_000)),
        2 => (rng.gen_range_i32(0, 100_000), 0),
        3 => {
            let x = rng.gen_range_i32(0, 100_000);
            (x, x)
        }
        4 => (1, rng.gen_range_i32(0, 100_000)),
        5 => (rng.gen_range_i32(0, 100_000), 1),
        6 => (100_000, rng.gen_range_i32(0, 100_000)),
        7 => (rng.gen_range_i32(0, 100_000), 100_000),
        8 => {
            // Fibonacci-like: worst case for Euclidean
            let a = rng.gen_range_i32(1, 75_025);
            let b = rng.gen_range_i32(1, 75_025);
            (a.min(100_000), b.min(100_000))
        }
        9 => {
            // small values
            let a = rng.gen_range_i32(0, 10);
            let b = rng.gen_range_i32(0, 10);
            (a, b)
        }
        _ => {
            let a = rng.gen_range_i32(0, 100_000);
            let b = rng.gen_range_i32(0, 100_000);
            (a, b)
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (a, b) = pick_for_mode(&mut rng, mode);
        // Ensure sum <= 200000 (always true since each <= 100000)
        let (num1, num2) = generate_test_case(a, b);
        println!("{{\"num1\": {}, \"num2\": {}}}", num1, num2);
    }
}
