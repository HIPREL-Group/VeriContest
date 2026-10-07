use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        0 <= n <= 10_000,
    ensures
        0 <= result <= 10_000,
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4 => 4,
        5 => 5,
        6 => 10_000,
        7 => 9_999,
        8 => rng.gen_range_i32(0, 30),
        9 => {
            // multiples of 5
            let k = rng.gen_range_i32(0, 2000);
            k * 5
        }
        10 => {
            // multiples of 25
            let k = rng.gen_range_i32(0, 400);
            k * 25
        }
        11 => {
            // multiples of 125
            let k = rng.gen_range_i32(0, 80);
            k * 125
        }
        12 => {
            // multiples of 625
            let k = rng.gen_range_i32(0, 16);
            k * 625
        }
        13 => {
            // one less than multiple of 5
            let k = rng.gen_range_i32(1, 2000);
            k * 5 - 1
        }
        14 => {
            // one more than multiple of 5
            let k = rng.gen_range_i32(0, 1999);
            k * 5 + 1
        }
        _ => rng.gen_range_i32(0, 10_000),
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
    let modes = 16usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let mut n = pick_for_mode(&mut rng, mode);
        if n < 0 {
            n = 0;
        }
        if n > 10_000 {
            n = 10_000;
        }
        let result = generate_test_case(n);
        println!("{{\"n\":{}}}", result);
    }
}