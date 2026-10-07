use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32) -> (n: i32)
    requires
        1 <= n_val <= 10000,
    ensures
        1 <= n <= 10000,
{
    n_val
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn pick_n_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 10000,
        4 => 9999,
        5 => rng.gen_range_i32(1, 10),
        6 => rng.gen_range_i32(2, 2) * rng.gen_range_i32(1, 5) * 2, // even-ish small
        7 => {
            // odd numbers
            let v = rng.gen_range_i32(1, 5000);
            2 * v - 1
        }
        8 => {
            // even numbers
            let v = rng.gen_range_i32(1, 5000);
            2 * v
        }
        9 => rng.gen_range_i32(9000, 10000),
        _ => rng.gen_range_i32(1, 10000),
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
        let mut n = pick_n_for_mode(&mut rng, mode);
        if n < 1 {
            n = 1;
        }
        if n > 10000 {
            n = 10000;
        }
        let out = generate_test_case(n);
        println!("{{\"n\":{}}}", out);
    }
}