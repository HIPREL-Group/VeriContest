use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32, k_val: i32) -> (result: (i32, i32))
    requires
        1 <= n_val <= 1000000000,
        1 <= k_val <= n_val,
    ensures
        1 <= result.0 <= 1000000000,
        1 <= result.1 <= result.0,
{
    (n_val, k_val)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn emit(n: i32, k: i32) {
    // clamp to safe values just in case
    let n = n.max(1).min(1_000_000_000);
    let k = k.max(1).min(n);
    let (nn, kk) = generate_test_case(n, k);
    println!("{{\"n\": {}, \"k\": {}}}", nn, kk);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);

    // Adversarial fixed cases
    let fixed: Vec<(i32, i32)> = vec![
        (1, 1),
        (13, 2),
        (13, 1),
        (13, 13),
        (10, 3),
        (10, 10),
        (100, 50),
        (100, 1),
        (100, 100),
        (1000000000, 1),
        (1000000000, 1000000000),
        (1000000000, 500000000),
        (1000000000, 999999999),
        (999999999, 999999999),
        (2, 1),
        (2, 2),
        (9, 9),
        (10, 1),
        (10, 2),
        (11, 2),
        (11, 3),
        (19, 10),
        (20, 11),
        (99, 50),
        (123456789, 1),
        (123456789, 123456789),
        (123456789, 61728394),
        (1000000000, 2),
        (1000000000, 999999998),
        (1, 1),
    ];

    for (n, k) in &fixed {
        emit(*n, *k);
    }

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let (n, k) = match mode {
            0 => {
                // small n
                let n = rng.gen_range_i32(1, 20);
                let k = rng.gen_range_i32(1, n);
                (n, k)
            }
            1 => {
                // medium n
                let n = rng.gen_range_i32(20, 10_000);
                let k = rng.gen_range_i32(1, n);
                (n, k)
            }
            2 => {
                // large n
                let n = rng.gen_range_i32(100_000, 1_000_000_000);
                let k = rng.gen_range_i32(1, n);
                (n, k)
            }
            3 => {
                // k = 1
                let n = rng.gen_range_i32(1, 1_000_000_000);
                (n, 1)
            }
            4 => {
                // k = n
                let n = rng.gen_range_i32(1, 1_000_000_000);
                (n, n)
            }
            5 => {
                // n = 10^9
                let n = 1_000_000_000;
                let k = rng.gen_range_i32(1, n);
                (n, k)
            }
            6 => {
                // n is power of 10
                let pows = [1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000];
                let n = pows[(rng.next_u64() as usize) % pows.len()];
                let k = rng.gen_range_i32(1, n);
                (n, k)
            }
            7 => {
                // n = 10^p - 1
                let pows = [9, 99, 999, 9999, 99999, 999999, 9999999, 99999999, 999999999];
                let n = pows[(rng.next_u64() as usize) % pows.len()];
                let k = rng.gen_range_i32(1, n);
                (n, k)
            }
            8 => {
                // k near middle
                let n = rng.gen_range_i32(10, 1_000_000_000);
                let k = n / 2 + rng.gen_range_i32(0, (n / 4).max(1));
                let k = k.max(1).min(n);
                (n, k)
            }
            _ => {
                // k close to n
                let n = rng.gen_range_i32(10, 1_000_000_000);
                let diff = rng.gen_range_i32(0, 10.min(n - 1));
                (n, n - diff)
            }
        };
        emit(n, k);
    }
}