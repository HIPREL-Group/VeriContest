use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, target: i32) -> (res: (i32, i32))
    requires
        1 <= n <= 1000000000,
        1 <= target <= 1000000000,
    ensures
        1 <= res.0 <= 1000000000,
        1 <= res.1 <= 1000000000,
{
    (n, target)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1, 1_000_000_000),
        2 => (1_000_000_000, 1),
        3 => (1_000_000_000, 1_000_000_000),
        4 => (rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 10)),
        5 => {
            // n <= target/2 case: target large, n small
            let t = rng.gen_range_i32(100, 1_000_000_000);
            let n = rng.gen_range_i32(1, t / 2);
            (n, t)
        }
        6 => {
            // n > target/2 case: target small, n large
            let t = rng.gen_range_i32(2, 100);
            let n = rng.gen_range_i32(t, 1_000_000_000);
            (n, t)
        }
        7 => {
            // n == target/2 boundary
            let t = rng.gen_range_i32(2, 1_000_000_000);
            let n = (t / 2).max(1);
            (n, t)
        }
        8 => {
            // n == target/2 + 1
            let t = rng.gen_range_i32(2, 1_000_000_000);
            let n = (t / 2 + 1).min(1_000_000_000);
            (n, t)
        }
        9 => {
            // target = 2 (edge)
            (rng.gen_range_i32(1, 1_000_000_000), 2)
        }
        10 => {
            // target = 1 (edge)
            (rng.gen_range_i32(1, 1_000_000_000), 1)
        }
        _ => (rng.gen_range_i32(1, 1_000_000_000), rng.gen_range_i32(1, 1_000_000_000)),
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
        let (n, target) = pick(&mut rng, mode);
        let n = if n < 1 { 1 } else if n > 1_000_000_000 { 1_000_000_000 } else { n };
        let target = if target < 1 { 1 } else if target > 1_000_000_000 { 1_000_000_000 } else { target };
        let (nn, tt) = generate_test_case(n, target);
        println!("{{\"n\": {}, \"target\": {}}}", nn, tt);
    }
}