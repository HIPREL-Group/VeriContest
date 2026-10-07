use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: usize, k_val: i32) -> (result: (usize, i32))
    requires
        1 <= n_val <= 10000,
        1 <= k_val <= 100,
    ensures
        1 <= result.0 <= 10000,
        1 <= result.1 <= 100,
        result.0 == n_val,
        result.1 == k_val,
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_case(rng: &mut Rng, mode: usize, idx: usize) -> (usize, i32) {
    match mode {
        0 => (1, 1),                                        // smallest
        1 => (1, 100),                                      // k max, n min
        2 => (10000, 1),                                    // n max, k min
        3 => (10000, 100),                                  // both max
        4 => (rng.gen_range_usize(1, 10), rng.gen_range_i32(1, 100)),  // small random
        5 => (rng.gen_range_usize(1, 100), 1),              // k=1
        6 => (1, rng.gen_range_i32(1, 100)),                // n=1
        7 => (rng.gen_range_usize(1, 10000), 100),          // k=100
        8 => (rng.gen_range_usize(5000, 10000), rng.gen_range_i32(1, 100)), // large n
        9 => (2, rng.gen_range_i32(1, 100)),                // n=2
        _ => {
            let n = rng.gen_range_usize(1, 10000);
            let k = rng.gen_range_i32(1, 100);
            let _ = idx;
            (n, k)
        }
    }
}

fn print_json(n: usize, k: i32) {
    println!("{{\"n\": {}, \"k\": {}}}", n, k);
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
        let (n, k) = pick_case(&mut rng, mode, t);
        let (nn, kk) = generate_test_case(n, k);
        print_json(nn, kk);
    }
}