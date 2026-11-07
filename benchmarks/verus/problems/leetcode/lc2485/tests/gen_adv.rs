use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32) -> (n: i32)
    requires
        1 <= n_val <= 1000,
    ensures
        1 <= n <= 1000,
{
    n_val
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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_n(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 4,
        4 => 6,
        5 => 8,
        6 => 1000,
        7 => 999,
        8 => {
            // Perfect square minus one pivots: known pivots exist when n(n+1)/2 is a triangular "square-ish"
            // Pivots known for n=1,8,49,288 (last two out of range). Use n=49.
            49
        }
        9 => {
            // small random
            rng.gen_range_i32(1, 20)
        }
        _ => rng.gen_range_i32(1, 1000),
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n_val = pick_n(&mut rng, mode, t);
        let clamped = if n_val < 1 { 1 } else if n_val > 1000 { 1000 } else { n_val };
        let n = generate_test_case(clamped);
        println!("{{\"n\":{}}}", n);
    }
}