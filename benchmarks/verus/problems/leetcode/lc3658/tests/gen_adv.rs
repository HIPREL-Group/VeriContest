use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1 <= n <= 1_000,
    ensures
        1 <= res <= 1_000,
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
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 1000,
        2 => 2,
        3 => 999,
        4 => rng.gen_range_i32(1, 10),
        5 => rng.gen_range_i32(990, 1000),
        6 => rng.gen_range_i32(1, 1000),
        7 => rng.gen_range_i32(100, 200),
        8 => {
            // power of 2
            let choices = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512];
            choices[(rng.next_u64() as usize) % choices.len()]
        }
        9 => {
            // primes
            let choices = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 97, 101, 997];
            choices[(rng.next_u64() as usize) % choices.len()]
        }
        _ => rng.gen_range_i32(1, 1000),
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
        let n = pick_for_mode(&mut rng, mode);
        let n = if n < 1 { 1 } else if n > 1000 { 1000 } else { n };
        let out = generate_test_case(n);
        println!("{{\"n\":{}}}", out);
    }
}