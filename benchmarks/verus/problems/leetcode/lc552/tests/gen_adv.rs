use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 100000,
    ensures
        1 <= result <= 100000,
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 100000,
        4 => 99999,
        5 => 10101,
        6 => rng.gen_range_i32(1, 10),
        7 => rng.gen_range_i32(1, 100),
        8 => rng.gen_range_i32(1, 1000),
        9 => rng.gen_range_i32(1, 100000),
        10 => rng.gen_range_i32(50000, 100000),
        11 => rng.gen_range_i32(1, 50),
        _ => rng.gen_range_i32(1, 100000),
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_for_mode(&mut rng, mode);
        let v = generate_test_case(n);
        println!("{{\"n\":{}}}", v);
    }
}