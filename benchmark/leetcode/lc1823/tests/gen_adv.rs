use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, k: i32) -> (result: (i32, i32))
    requires
        1 <= k <= n <= 500,
    ensures
        1 <= result.1 <= result.0 <= 500,
        result.0 == n,
        result.1 == k,
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn pick_nk(rng: &mut Rng, mode: usize, t: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (2, 1),
        2 => (2, 2),
        3 => (500, 1),
        4 => (500, 500),
        5 => {
            let n = rng.gen_range_i32(1, 500);
            (n, n)
        }
        6 => {
            let n = rng.gen_range_i32(1, 500);
            (n, 1)
        }
        7 => {
            let n = rng.gen_range_i32(2, 500);
            (n, 2)
        }
        8 => {
            let n = 500;
            let k = rng.gen_range_i32(1, 500);
            (n, k)
        }
        9 => {
            // small n
            let n = rng.gen_range_i32(1, 10);
            let k = rng.gen_range_i32(1, n);
            (n, k)
        }
        10 => {
            // n = k/2 range
            let n = rng.gen_range_i32(2, 500);
            let k = rng.gen_range_i32(1, n);
            // bias k close to n
            let k2 = if k > n - 3 { k } else { n - (t as i32 % 3) };
            let k2 = if k2 < 1 { 1 } else { k2 };
            let k2 = if k2 > n { n } else { k2 };
            (n, k2)
        }
        _ => {
            let n = rng.gen_range_i32(1, 500);
            let k = rng.gen_range_i32(1, n);
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
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, k) = pick_nk(&mut rng, mode, t);
        let (n2, k2) = generate_test_case(n, k);
        println!("{{\"n\": {}, \"k\": {}}}", n2, k2);
    }
}