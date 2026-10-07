use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 100_000,
    ensures
        1 <= result <= 100_000,
        result == n,
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_n_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 4,
        4 => 5,
        5 => 100_000,
        6 => 99_999,
        7 => {
            // small even
            let v = rng.gen_range_i32(1, 50);
            v * 2
        }
        8 => {
            // small odd
            let v = rng.gen_range_i32(0, 50);
            v * 2 + 1
        }
        9 => {
            // large random
            rng.gen_range_i32(50_000, 100_000)
        }
        10 => {
            // small random
            rng.gen_range_i32(1, 20)
        }
        11 => {
            // powers of two
            let k = (t % 17) as u32;
            let v = 1i32 << k;
            if v > 100_000 { 100_000 } else { v }
        }
        _ => rng.gen_range_i32(1, 100_000),
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_n_for_mode(&mut rng, mode, t);
        let n = if n < 1 { 1 } else if n > 100_000 { 100_000 } else { n };
        let out = generate_test_case(n);
        println!("{{\"n\":{}}}", out);
    }
}