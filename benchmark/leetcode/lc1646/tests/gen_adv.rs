use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32) -> (n: i32)
    requires
        0 <= n_val <= 100,
    ensures
        0 <= n <= 100,
{
    n_val
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
        3 => 3,
        4 => 100,
        5 => 99,
        6 => rng.gen_range_i32(0, 10),
        7 => rng.gen_range_i32(90, 100),
        8 => rng.gen_range_i32(0, 100),
        9 => {
            // powers of 2
            let choices = [1i32, 2, 4, 8, 16, 32, 64];
            choices[(rng.next_u64() as usize) % choices.len()]
        }
        _ => rng.gen_range_i32(0, 100),
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
        let raw = pick_for_mode(&mut rng, mode);
        let clamped = if raw < 0 { 0 } else if raw > 100 { 100 } else { raw };
        let n = generate_test_case(clamped);
        println!("{{\"n\": {}}}", n);
    }
}