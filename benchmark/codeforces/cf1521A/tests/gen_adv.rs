use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i64, b: i64) -> (res: (i64, i64))
    requires
        1 <= a <= 1_000_000_000,
        1 <= b <= 1_000_000_000,
        (a as int) * (b as int) <= i64::MAX as int,
        (a as int) * (b as int + 1) <= i64::MAX as int,
    ensures
        1 <= res.0 <= 1_000_000_000,
        1 <= res.1 <= 1_000_000_000,
        (res.0 as int) * (res.1 as int) <= i64::MAX as int,
        (res.0 as int) * (res.1 as int + 1) <= i64::MAX as int,
{
    (a, b)
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

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

// Given a target maximum for a*(b+1), pick random a and b.
// We need a*(b+1) <= i64::MAX. i64::MAX ~ 9.22e18.
// With a, b <= 1e9, a*(b+1) <= 1e9 * (1e9+1) ~ 1e18 < i64::MAX. Always safe.

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i64, i64) {
    match mode {
        0 => (1, 1),                                    // b == 1, should return NO
        1 => (1, 2),                                    // smallest b != 1
        2 => (1_000_000_000, 1_000_000_000),            // max a, max b
        3 => (1_000_000_000, 1),                        // max a, b == 1 -> NO
        4 => (1, 1_000_000_000),                        // a = 1, max b
        5 => (rng.gen_range_i64(1, 1_000_000_000), 1),  // random a, b == 1 -> NO
        6 => {
            let a = rng.gen_range_i64(1, 1_000_000_000);
            let b = rng.gen_range_i64(2, 1_000_000_000);
            (a, b)
        }
        7 => (2, 2),                                    // small both
        8 => {
            // large product edge
            let a = rng.gen_range_i64(900_000_000, 1_000_000_000);
            let b = rng.gen_range_i64(900_000_000, 1_000_000_000);
            (a, b)
        }
        9 => {
            // a = b
            let a = rng.gen_range_i64(2, 1_000_000_000);
            (a, a)
        }
        _ => {
            let a = rng.gen_range_i64(1, 1_000_000_000);
            let b = rng.gen_range_i64(1, 1_000_000_000);
            (a, b)
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
        let (a, b) = pick_for_mode(&mut rng, mode);
        let (oa, ob) = generate_test_case(a, b);
        println!("{{\"a\": {}, \"b\": {}}}", oa, ob);
    }
}