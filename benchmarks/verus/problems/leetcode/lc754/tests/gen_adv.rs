use vstd::prelude::*;

verus! {

pub fn generate_test_case(target: i32) -> (res: i32)
    requires
        -1_000_000_000 <= target <= 1_000_000_000,
        target != 0,
    ensures
        -1_000_000_000 <= res <= 1_000_000_000,
        res != 0,
{
    target
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
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => {
            // small positive targets
            rng.gen_range_i32(1, 20)
        }
        1 => {
            // small negative targets
            rng.gen_range_i32(-20, -1)
        }
        2 => {
            // target = 1
            1
        }
        3 => {
            // target = -1
            -1
        }
        4 => {
            // target = i32 max-ish
            1_000_000_000
        }
        5 => {
            // target = min
            -1_000_000_000
        }
        6 => {
            // triangular numbers: 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, ...
            let n = rng.gen_range_i32(1, 44721); // n*(n+1)/2 <= 1e9 roughly
            let t = (n as i64) * (n as i64 + 1) / 2;
            let t = if t > 1_000_000_000 { 1_000_000_000 } else { t };
            let sign = if rng.next_u64() % 2 == 0 { 1i64 } else { -1i64 };
            let v = sign * t;
            if v == 0 { 1 } else { v as i32 }
        }
        7 => {
            // triangular + 1 (odd difference)
            let n = rng.gen_range_i32(1, 44720);
            let t = (n as i64) * (n as i64 + 1) / 2 + 1;
            let t = if t > 1_000_000_000 { 1_000_000_000 } else { t };
            let sign = if rng.next_u64() % 2 == 0 { 1i64 } else { -1i64 };
            let v = sign * t;
            if v == 0 { 1 } else { v as i32 }
        }
        8 => {
            // medium random
            let mut v = rng.gen_range_i32(-1000, 1000);
            if v == 0 { v = 1; }
            v
        }
        9 => {
            // large random
            let mut v = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            if v == 0 { v = 1; }
            v
        }
        _ => {
            let mut v = rng.gen_range_i32(-100_000, 100_000);
            if v == 0 { v = 1; }
            v
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
        let mut target = pick_for_mode(&mut rng, mode);
        // clamp to valid range and nonzero
        if target > 1_000_000_000 { target = 1_000_000_000; }
        if target < -1_000_000_000 { target = -1_000_000_000; }
        if target == 0 { target = 1; }

        let out = generate_test_case(target);
        println!("{{\"target\":{}}}", out);
    }
}