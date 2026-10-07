use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        2 <= n <= 58,
    ensures
        2 <= result <= 58,
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 2,
        1 => 3,
        2 => 4,
        3 => 58,
        4 => 57,
        5 => 10,
        6 => {
            // Small values
            rng.gen_range_i32(2, 10)
        }
        7 => {
            // Medium values
            rng.gen_range_i32(10, 30)
        }
        8 => {
            // Large values
            rng.gen_range_i32(40, 58)
        }
        9 => {
            // Values near multiples of 3
            let base = 3 * ((t as i32 % 18) + 1);
            if base < 2 { 2 } else if base > 58 { 58 } else { base }
        }
        _ => {
            rng.gen_range_i32(2, 58)
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

    // First, emit every value from 2..=58 once for full coverage
    for n in 2i32..=58 {
        let v = generate_test_case(n);
        println!("{{\"n\":{}}}", v);
    }

    let remaining = if total > 57 { total - 57 } else { 0 };
    for t in 0..remaining {
        let mode = t % modes;
        let n = pick_for_mode(&mut rng, mode, t);
        let v = generate_test_case(n);
        println!("{{\"n\":{}}}", v);
    }
}