use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        0 <= n <= 1_000_000_000,
    ensures
        0 <= result <= 1_000_000_000,
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

    fn gen_range(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize, idx: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4 => 4,
        5 => 1_000_000_000,
        6 => 999_999_999,
        7 => {
            // perfect squares
            let k = rng.gen_range(1, 31622);
            (k * k) as i32
        }
        8 => {
            // one less than perfect square
            let k = rng.gen_range(2, 31622);
            (k * k - 1) as i32
        }
        9 => {
            // one more than perfect square
            let k = rng.gen_range(1, 31621);
            (k * k + 1) as i32
        }
        10 => {
            // small values
            rng.gen_range(0, 100) as i32
        }
        11 => {
            // medium values
            rng.gen_range(100, 100_000) as i32
        }
        _ => {
            // random over full range
            let _ = idx;
            rng.gen_range(0, 1_000_000_000) as i32
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
    let modes = 13usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_for_mode(&mut rng, mode, t);
        let n_clamped = if n < 0 { 0 } else if n > 1_000_000_000 { 1_000_000_000 } else { n };
        let result = generate_test_case(n_clamped);
        println!("{{\"n\":{}}}", result);
    }
}