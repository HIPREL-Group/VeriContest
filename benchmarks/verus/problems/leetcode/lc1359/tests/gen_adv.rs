use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 500,
    ensures
        1 <= result <= 500,
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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn pick_n(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 500,
        4 => 499,
        5 => 4,
        6 => 10,
        7 => 100,
        8 => 250,
        9 => rng.gen_range_i32(1, 500),
        _ => {
            let v = (t % 500) as i32 + 1;
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_n(&mut rng, mode, t);
        let n_clamped = if n < 1 { 1 } else if n > 500 { 500 } else { n };
        let out = generate_test_case(n_clamped);
        println!("{{\"n\":{}}}", out);
    }
}