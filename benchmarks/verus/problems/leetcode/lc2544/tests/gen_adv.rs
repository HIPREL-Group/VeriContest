use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 1_000_000_000,
    ensures
        1 <= result <= 1_000_000_000,
{
    n
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
        lo + v as i32
    }
}

fn adversarial(mode: usize, rng: &mut Rng) -> i32 {
    match mode {
        0 => 1,
        1 => 1_000_000_000,
        2 => 9,
        3 => 10,
        4 => 99,
        5 => 100,
        6 => 999_999_999,
        7 => {
            // all same digit
            let d = rng.gen_range_i32(1, 9);
            let len = rng.gen_range_i32(1, 9) as usize;
            let mut v: i32 = 0;
            for _ in 0..len {
                v = v * 10 + d;
            }
            v
        }
        8 => {
            // power of 10
            let p = rng.gen_range_i32(0, 9) as u32;
            10i32.pow(p)
        }
        9 => {
            // random small
            rng.gen_range_i32(1, 999)
        }
        10 => {
            // random medium
            rng.gen_range_i32(1000, 999_999)
        }
        _ => {
            // random large
            rng.gen_range_i32(1, 1_000_000_000)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 12usize;
    let total = 200usize;

    for t in 0..total {
        let n = if t < modes * 2 {
            adversarial(t % modes, &mut rng)
        } else {
            let mode = (t % (modes + 1)) as usize;
            if mode < modes {
                adversarial(mode, &mut rng)
            } else {
                rng.gen_range_i32(1, 1_000_000_000)
            }
        };
        let out = generate_test_case(n);
        println!("{{\"n\": {}}}", out);
    }
}