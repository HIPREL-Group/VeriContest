use vstd::prelude::*;

verus! {

pub fn generate_test_case(k_val: i64, x_val: i32) -> (result: (i64, i32))
    requires
        1 <= k_val <= 1_000_000_000_000_000,
        1 <= x_val <= 8,
    ensures
        1 <= result.0 <= 1_000_000_000_000_000,
        1 <= result.1 <= 8,
{
    (k_val, x_val)
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

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn pick_case(rng: &mut Rng, mode: usize) -> (i64, i32) {
    match mode {
        0 => (1, 1),
        1 => (1, 8),
        2 => (1_000_000_000_000_000, 1),
        3 => (1_000_000_000_000_000, 8),
        4 => (rng.gen_range_i64(1, 100), rng.gen_range_i32(1, 8)),
        5 => (rng.gen_range_i64(1, 1000), 1),
        6 => (rng.gen_range_i64(1, 1_000_000), rng.gen_range_i32(1, 8)),
        7 => (rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i32(1, 8)),
        8 => (rng.gen_range_i64(1, 1_000_000_000_000), rng.gen_range_i32(1, 8)),
        9 => (rng.gen_range_i64(1, 1_000_000_000_000_000), rng.gen_range_i32(1, 8)),
        10 => (9, 1),
        11 => (7, 2),
        12 => (rng.gen_range_i64(1, 1_000_000_000_000_000), 1),
        13 => (rng.gen_range_i64(1, 1_000_000_000_000_000), 8),
        _ => (rng.gen_range_i64(1, 1_000_000_000_000_000), rng.gen_range_i32(1, 8)),
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
    let modes = 15usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (mut k, mut x) = pick_case(&mut rng, mode);
        if k < 1 { k = 1; }
        if k > 1_000_000_000_000_000 { k = 1_000_000_000_000_000; }
        if x < 1 { x = 1; }
        if x > 8 { x = 8; }

        let (ok_k, ok_x) = generate_test_case(k, x);
        println!("{{\"k\":{},\"x\":{}}}", ok_k, ok_x);
    }
}