use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32, k_val: i32) -> (result: (i32, i32))
    requires
        1 <= n_val <= 1000,
        1 <= k_val <= 1000,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= 1000,
{
    (n_val, k_val)
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

fn pick(mode: usize, rng: &mut Rng) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1000, 1000),
        2 => (1, 1000),
        3 => (1000, 1),
        4 => (2, 2),
        5 => (rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 10)),
        6 => (rng.gen_range_i32(990, 1000), rng.gen_range_i32(990, 1000)),
        7 => (rng.gen_range_i32(1, 1000), 1),
        8 => (1, rng.gen_range_i32(1, 1000)),
        9 => (500, 500),
        _ => (rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000)),
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
        let (n, k) = pick(mode, &mut rng);
        let (nn, kk) = generate_test_case(n, k);
        println!("{{\"n\":{},\"k\":{}}}", nn, kk);
    }
}