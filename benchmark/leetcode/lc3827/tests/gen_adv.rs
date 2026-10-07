use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        0 <= n <= 1000,
    ensures
        0 <= res <= 1000,
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

fn pick_n(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4 => 4,
        5 => 7,
        6 => 15,
        7 => 31,
        8 => 1000,
        9 => 999,
        10 => 512,
        11 => 511,
        12 => rng.gen_range_i32(0, 10),
        13 => rng.gen_range_i32(0, 100),
        _ => rng.gen_range_i32(0, 1000),
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
    let modes = 15usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_n(&mut rng, mode);
        let n_clamped = if n < 0 { 0 } else if n > 1000 { 1000 } else { n };
        let out = generate_test_case(n_clamped);
        println!("{{\"n\":{}}}", out);
    }
}