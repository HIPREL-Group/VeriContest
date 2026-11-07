use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        2 <= n <= 1000,
    ensures
        2 <= result <= 1000,
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
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_n(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 2,
        1 => 3,
        2 => 4,
        3 => 1000,
        4 => 999,
        5 => 1000,
        6 => 5 + (t as i32 % 10),
        7 => rng.gen_range_i32(2, 1000),
        8 => rng.gen_range_i32(2, 50),
        9 => rng.gen_range_i32(950, 1000),
        _ => rng.gen_range_i32(2, 1000),
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
        let n = pick_n(&mut rng, mode, t);
        let n_valid = generate_test_case(n);
        println!("{{\"n\":{}}}", n_valid);
    }
}