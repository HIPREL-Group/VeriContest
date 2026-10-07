use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, k: i32) -> (result: (i32, i32))
    requires
        2 <= n <= 50,
        1 <= k <= 50,
    ensures
        2 <= result.0 <= 50,
        1 <= result.1 <= 50,
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
        lo + (self.next_u64() % span) as i32
    }
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (2, 1),
        1 => (2, 50),
        2 => (50, 1),
        3 => (50, 50),
        4 => (rng.gen_range_i32(2, 50), 1),
        5 => (rng.gen_range_i32(2, 50), 50),
        6 => {
            let n = rng.gen_range_i32(2, 50);
            // k = n-1, reaches end
            (n, n - 1)
        }
        7 => {
            let n = rng.gen_range_i32(2, 50);
            // k = 2n-2, full cycle
            let m = 2 * n - 2;
            let k = if m >= 1 && m <= 50 { m } else { 1 };
            (n, k)
        }
        8 => {
            let n = rng.gen_range_i32(3, 50);
            (n, n)
        }
        9 => {
            // small n large k
            (2, rng.gen_range_i32(1, 50))
        }
        _ => {
            (rng.gen_range_i32(2, 50), rng.gen_range_i32(1, 50))
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
        let (n, k) = pick(&mut rng, mode);
        let n = if n < 2 { 2 } else if n > 50 { 50 } else { n };
        let k = if k < 1 { 1 } else if k > 50 { 50 } else { k };
        let (nn, kk) = generate_test_case(n, k);
        println!("{{\"n\": {}, \"k\": {}}}", nn, kk);
    }
}