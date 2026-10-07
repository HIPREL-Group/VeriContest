use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32) -> (result: i32)
    requires
        1 <= x <= 1000,
    ensures
        1 <= result <= 1000,
{
    x
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
        0 => 1,
        1 => 1000,
        2 => 2,
        3 => 999,
        4 => 10,
        5 => 100,
        6 => rng.gen_range_i32(1, 10),
        7 => rng.gen_range_i32(990, 1000),
        8 => rng.gen_range_i32(1, 1000),
        9 => rng.gen_range_i32(100, 999),
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let x = pick_for_mode(&mut rng, mode);
        let x = if x < 1 { 1 } else if x > 1000 { 1000 } else { x };
        let r = generate_test_case(x);
        println!("{{\"num\":{}}}", r);
    }
}