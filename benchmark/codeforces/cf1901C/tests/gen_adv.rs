use vstd::prelude::*;

verus! {

pub fn generate_test_case(d_val: i64) -> (d: i64)
    requires
        0 <= d_val <= 1_000_000_000,
    ensures
        d >= 0,
{
    d_val
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: if seed == 0 { 1 } else { seed } }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i64 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 1_000_000_000,
        4 => 999_999_999,
        5 => {
            // power of two
            let k = rng.gen_range_i64(0, 29);
            1i64 << k
        }
        6 => {
            // power of two minus one
            let k = rng.gen_range_i64(1, 30);
            (1i64 << k) - 1
        }
        7 => {
            // power of two plus one
            let k = rng.gen_range_i64(1, 29);
            (1i64 << k) + 1
        }
        8 => {
            // small values
            rng.gen_range_i64(0, 20)
        }
        9 => {
            // medium values
            rng.gen_range_i64(0, 1_000_000)
        }
        _ => {
            // full range
            rng.gen_range_i64(0, 1_000_000_000)
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
        let d_val = pick_for_mode(&mut rng, mode);
        let d = generate_test_case(d_val);
        println!("{{\"d\":{}}}", d);
    }
}