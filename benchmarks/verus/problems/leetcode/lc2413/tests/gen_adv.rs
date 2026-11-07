use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 150,
    ensures
        1 <= result <= 150,
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

fn pick_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 150,
        3 => 149,
        4 => 3,
        5 => {
            // even numbers
            let v = rng.gen_range_i32(1, 75) * 2;
            if v > 150 { 150 } else { v }
        }
        6 => {
            // odd numbers
            let v = rng.gen_range_i32(0, 74) * 2 + 1;
            if v > 150 { 149 } else { v }
        }
        7 => {
            // powers of 2
            let powers = [1, 2, 4, 8, 16, 32, 64, 128];
            powers[t % powers.len()]
        }
        8 => {
            // small values
            rng.gen_range_i32(1, 10)
        }
        9 => {
            // near boundary
            rng.gen_range_i32(145, 150)
        }
        _ => rng.gen_range_i32(1, 150),
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
        let n = pick_for_mode(&mut rng, mode, t);
        let n_clamped = if n < 1 { 1 } else if n > 150 { 150 } else { n };
        let result = generate_test_case(n_clamped);
        println!("{{\"n\":{}}}", result);
    }
}