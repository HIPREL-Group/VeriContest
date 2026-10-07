use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 1_000_000,
    ensures
        1 <= result <= 1_000_000,
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 1_000_000,
        2 => 99,
        3 => 23,
        4 => {
            // powers of 10 - contain 0 digits
            let pows = [10, 100, 1000, 10000, 100000, 1000000];
            pows[(rng.next_u64() as usize) % pows.len()]
        }
        5 => {
            // single digit
            rng.gen_range_i32(1, 9)
        }
        6 => {
            // two digit
            rng.gen_range_i32(10, 99)
        }
        7 => {
            // contains a zero digit
            let bases = [10, 20, 30, 100, 101, 200, 1000, 10005, 100007, 500000];
            bases[(rng.next_u64() as usize) % bases.len()]
        }
        8 => {
            // all 9s
            let vals = [9, 99, 999, 9999, 99999, 999999];
            vals[(rng.next_u64() as usize) % vals.len()]
        }
        9 => {
            // near boundary
            rng.gen_range_i32(999_990, 1_000_000)
        }
        _ => {
            rng.gen_range_i32(1, 1_000_000)
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
        let n = pick_for_mode(&mut rng, mode);
        let n_clamped = if n < 1 { 1 } else if n > 1_000_000 { 1_000_000 } else { n };
        let result = generate_test_case(n_clamped);
        println!("{{\"n\":{}}}", result);
    }
}