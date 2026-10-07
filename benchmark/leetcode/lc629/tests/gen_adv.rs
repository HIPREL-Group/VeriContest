use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32, k_val: i32) -> (result: (i32, i32))
    requires
        1 <= n_val <= 1000,
        0 <= k_val <= 1000,
    ensures
        1 <= result.0 <= 1000,
        0 <= result.1 <= 1000,
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 0),
        1 => (1000, 0),
        2 => (1000, 1000),
        3 => (1, rng.gen_range_i32(0, 1000)),
        4 => (rng.gen_range_i32(1, 1000), 0),
        5 => (rng.gen_range_i32(1, 10), rng.gen_range_i32(0, 10)),
        6 => (2, rng.gen_range_i32(0, 1000)),
        7 => (3, rng.gen_range_i32(0, 3)),
        8 => (1000, rng.gen_range_i32(0, 1000)),
        9 => {
            let n = rng.gen_range_i32(1, 1000);
            let maxk = if n >= 2 { (n * (n - 1)) / 2 } else { 0 };
            let cap = if maxk > 1000 { 1000 } else { maxk };
            let k = if cap > 0 { rng.gen_range_i32(0, cap) } else { 0 };
            (n, k)
        }
        _ => {
            let n = rng.gen_range_i32(1, 1000);
            let k = rng.gen_range_i32(0, 1000);
            (n, k)
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
        let (n, k) = pick_for_mode(&mut rng, mode);
        let (nn, kk) = generate_test_case(n, k);
        println!("{{\"n\": {}, \"k\": {}}}", nn, kk);
    }
}