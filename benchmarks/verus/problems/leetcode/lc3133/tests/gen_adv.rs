use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32, x_val: i32) -> (result: (i32, i32))
    requires
        1 <= n_val <= 100_000_000,
        1 <= x_val <= 100_000_000,
    ensures
        1 <= result.0 <= 100_000_000,
        1 <= result.1 <= 100_000_000,
{
    (n_val, x_val)
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (100_000_000, 100_000_000),
        2 => (1, 100_000_000),
        3 => (100_000_000, 1),
        4 => (rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 10)),
        5 => (rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100)),
        6 => {
            // Power-of-two x
            let bits = rng.gen_range_i32(0, 26);
            let x = 1i32 << bits;
            (rng.gen_range_i32(1, 100_000_000), x)
        }
        7 => {
            // All-ones-ish x
            let bits = rng.gen_range_i32(1, 26);
            let x = (1i32 << bits) - 1;
            (rng.gen_range_i32(1, 100_000_000), x.max(1))
        }
        8 => {
            // Large n, small x
            (rng.gen_range_i32(50_000_000, 100_000_000), rng.gen_range_i32(1, 10))
        }
        9 => {
            // Small n, large x
            (rng.gen_range_i32(1, 5), rng.gen_range_i32(50_000_000, 100_000_000))
        }
        _ => (rng.gen_range_i32(1, 100_000_000), rng.gen_range_i32(1, 100_000_000)),
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
        let (n, x) = pick_for_mode(&mut rng, mode);
        let n_clamped = if n < 1 { 1 } else if n > 100_000_000 { 100_000_000 } else { n };
        let x_clamped = if x < 1 { 1 } else if x > 100_000_000 { 100_000_000 } else { x };
        let (nn, xx) = generate_test_case(n_clamped, x_clamped);
        println!("{{\"n\": {}, \"x\": {}}}", nn, xx);
    }
}