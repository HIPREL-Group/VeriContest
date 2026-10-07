use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 50_000,
    ensures
        1 <= result <= 50_000,
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_n(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 9,
        3 => 10,
        4 => 11,
        5 => 13,
        6 => 99,
        7 => 100,
        8 => 101,
        9 => 999,
        10 => 1000,
        11 => 9999,
        12 => 10000,
        13 => 49999,
        14 => 50000,
        15 => rng.gen_range_i32(1, 100),
        16 => rng.gen_range_i32(1, 1000),
        17 => rng.gen_range_i32(1, 10000),
        18 => rng.gen_range_i32(1, 50000),
        _ => rng.gen_range_i32(1, 50000),
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
    let modes = 20usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_n(&mut rng, mode);
        let n = if n < 1 { 1 } else if n > 50_000 { 50_000 } else { n };
        let out = generate_test_case(n);
        println!("{{\"n\":{}}}", out);
    }
}