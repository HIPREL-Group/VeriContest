use vstd::prelude::*;

verus! {

pub fn generate_test_case(low: i32, high: i32) -> (result: (i32, i32))
    requires
        1 <= low <= high <= 10_000,
    ensures
        1 <= result.0 <= result.1 <= 10_000,
{
    (low, high)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 100),
        1 => (1200, 1230),
        2 => (1, 1),
        3 => (1, 10_000),
        4 => (10_000, 10_000),
        5 => (9999, 10_000),
        6 => {
            let lo = rng.gen_range_i32(1, 99);
            let hi = rng.gen_range_i32(lo, 99);
            (lo, hi)
        }
        7 => {
            let lo = rng.gen_range_i32(1000, 9999);
            let hi = rng.gen_range_i32(lo, 9999);
            (lo, hi)
        }
        8 => {
            let lo = rng.gen_range_i32(100, 999);
            let hi = rng.gen_range_i32(lo, 999);
            (lo, hi)
        }
        9 => {
            let lo = rng.gen_range_i32(1, 10_000);
            let hi = rng.gen_range_i32(lo, 10_000);
            (lo, hi)
        }
        _ => {
            let x = rng.gen_range_i32(1, 10_000);
            (x, x)
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
        let (lo, hi) = pick_case(&mut rng, mode);
        let (low, high) = generate_test_case(lo, hi);
        println!("{{\"low\":{},\"high\":{}}}", low, high);
    }
}