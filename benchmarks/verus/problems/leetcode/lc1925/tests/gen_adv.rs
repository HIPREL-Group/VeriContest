use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 250,
    ensures
        1 <= result <= 250,
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_n(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 5,
        3 => 10,
        4 => 250,
        5 => 249,
        6 => rng.gen_range_i32(1, 10),
        7 => rng.gen_range_i32(200, 250),
        8 => rng.gen_range_i32(100, 200),
        9 => rng.gen_range_i32(50, 150),
        _ => rng.gen_range_i32(1, 250),
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
        let n = pick_n(&mut rng, mode);
        let clamped = if n < 1 {
            1
        } else if n > 250 {
            250
        } else {
            n
        };
        let out = generate_test_case(clamped);
        println!("{{\"n\":{}}}", out);
    }
}