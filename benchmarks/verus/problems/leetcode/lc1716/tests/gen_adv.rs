use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 1000,
    ensures
        1 <= result <= 1000,
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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 1000,
        2 => 7,
        3 => 8,
        4 => 14,
        5 => 28,
        6 => {
            // multiples of 7
            let k = (t % 142) + 1;
            (k * 7) as i32
        }
        7 => {
            // one more than multiples of 7
            let k = (t % 142) + 1;
            ((k * 7) + 1) as i32
        }
        8 => {
            // small values
            rng.gen_range_i32(1, 20)
        }
        9 => {
            // large values near boundary
            rng.gen_range_i32(990, 1000)
        }
        _ => {
            rng.gen_range_i32(1, 1000)
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_for_mode(&mut rng, mode, t);
        let n_clamped = if n < 1 { 1 } else if n > 1000 { 1000 } else { n };
        let val = generate_test_case(n_clamped);
        println!("{{\"n\":{}}}", val);
    }
}