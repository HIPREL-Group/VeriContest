use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1 <= n as int <= 2_147_483_647,
    ensures
        1 <= res as int <= 2_147_483_647,
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_test(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 4,
        4 => 5,
        5 => 2_147_483_647,
        6 => 2_147_483_644,
        7 => {
            // multiples of 4
            let k = rng.gen_range_i32(1, 536_870_911);
            k.saturating_mul(4).max(4)
        }
        8 => {
            // not multiples of 4
            let k = rng.gen_range_i32(1, 536_870_911);
            let v = k.saturating_mul(4).max(4);
            if v == i32::MAX { v - 1 } else { v + 1 }
        }
        9 => {
            // small random
            rng.gen_range_i32(1, 100)
        }
        10 => {
            // near max
            let offset = rng.gen_range_i32(0, 10);
            2_147_483_647 - offset
        }
        _ => {
            let lo = 1;
            let hi = 2_147_483_647;
            let span = (hi as i64 - lo as i64 + 1) as u64;
            let v = rng.next_u64() % span;
            (lo as i64 + v as i64) as i32
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
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n_val = pick_test(&mut rng, mode, t);
        let n_clamped = if n_val < 1 { 1 } else { n_val };
        let n = generate_test_case(n_clamped);
        println!("{{\"n\": {}}}", n);
    }
}