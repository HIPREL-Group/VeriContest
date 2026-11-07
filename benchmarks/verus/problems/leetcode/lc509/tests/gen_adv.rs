use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        0 <= n <= 30,
    ensures
        0 <= res <= 30,
        res == n,
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 30,
        4 => 29,
        5 => 28,
        6 => 3,
        7 => rng.gen_range_i32(0, 30),
        8 => rng.gen_range_i32(0, 10),
        9 => rng.gen_range_i32(20, 30),
        _ => rng.gen_range_i32(0, 30),
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
        let n = pick_for_mode(&mut rng, mode);
        let n_ok = if n < 0 { 0 } else if n > 30 { 30 } else { n };
        let val = generate_test_case(n_ok);
        println!("{{\"n\":{}}}", val);
    }
}