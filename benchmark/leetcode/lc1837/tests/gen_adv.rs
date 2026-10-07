use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, k: i32) -> (result: (i32, i32))
    requires
        1 <= n <= 100,
        2 <= k <= 10,
    ensures
        1 <= result.0 <= 100,
        2 <= result.1 <= 10,
{
    (n, k)
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_test(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 2),
        1 => (1, 10),
        2 => (100, 2),
        3 => (100, 10),
        4 => (rng.gen_range_i32(1, 100), 2),
        5 => (rng.gen_range_i32(1, 100), 10),
        6 => {
            // powers of k - boundary cases
            let k = rng.gen_range_i32(2, 10);
            let mut p = 1i32;
            while p * k <= 100 {
                p *= k;
            }
            (p, k)
        }
        7 => {
            // k^m - 1 style
            let k = rng.gen_range_i32(2, 10);
            let mut p = 1i32;
            while p * k <= 100 {
                p *= k;
            }
            let v = if p > 1 { p - 1 } else { 1 };
            (v, k)
        }
        8 => {
            // n == k
            let k = rng.gen_range_i32(2, 10);
            (k, k)
        }
        9 => {
            // n < k
            let k = rng.gen_range_i32(2, 10);
            let n = rng.gen_range_i32(1, k - 1);
            (n, k)
        }
        _ => {
            let n = rng.gen_range_i32(1, 100);
            let k = rng.gen_range_i32(2, 10);
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
        let (n, k) = pick_test(&mut rng, mode);
        let (nn, kk) = generate_test_case(n, k);
        println!("{{\"n\": {}, \"k\": {}}}", nn, kk);
    }
}