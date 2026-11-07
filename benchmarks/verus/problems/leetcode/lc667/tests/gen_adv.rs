use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, k: i32) -> (result: (i32, i32))
    requires
        1 <= k < n <= 10_000,
    ensures
        ({
            let (nn, kk) = result;
            1 <= kk < nn <= 10_000
        }),
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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_case(rng: &mut Rng, mode: usize, idx: usize) -> (i32, i32) {
    match mode {
        0 => (2, 1),
        1 => (10_000, 1),
        2 => (10_000, 9_999),
        3 => (10_000, 5_000),
        4 => {
            let n = rng.gen_range_i32(2, 10_000);
            (n, 1)
        }
        5 => {
            let n = rng.gen_range_i32(2, 10_000);
            (n, n - 1)
        }
        6 => {
            let n = rng.gen_range_i32(3, 10_000);
            let k = rng.gen_range_i32(1, n - 1);
            (n, k)
        }
        7 => {
            let small = (3 + (idx % 10)) as i32;
            let k = rng.gen_range_i32(1, small - 1);
            (small, k)
        }
        8 => {
            let n = rng.gen_range_i32(100, 1000);
            let k = n / 2;
            (n, k)
        }
        9 => {
            let n = rng.gen_range_i32(2, 50);
            let k = rng.gen_range_i32(1, n - 1);
            (n, k)
        }
        _ => {
            let n = rng.gen_range_i32(2, 10_000);
            let k = rng.gen_range_i32(1, n - 1);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, k) = pick_case(&mut rng, mode, t);
        let (nn, kk) = generate_test_case(n, k);
        println!("{{\"n\": {}, \"k\": {}}}", nn, kk);
    }
}