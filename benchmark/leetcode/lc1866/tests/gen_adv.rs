use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, k: i32) -> (result: (i32, i32))
    requires
        1 <= n <= 1000,
        1 <= k <= n,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= result.0,
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
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_case(rng: &mut Rng, mode: usize, idx: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1000, 1000),
        2 => (1000, 1),
        3 => (1000, 500),
        4 => {
            let n = rng.gen_range_i32(1, 1000);
            (n, n)
        }
        5 => {
            let n = rng.gen_range_i32(1, 1000);
            (n, 1)
        }
        6 => {
            let n = rng.gen_range_i32(2, 1000);
            (n, n - 1)
        }
        7 => {
            let n = 2 + (idx as i32 % 20);
            let k = 1 + (idx as i32 % n);
            (n, k)
        }
        8 => {
            let n = rng.gen_range_i32(1, 1000);
            let k = rng.gen_range_i32(1, n);
            (n, k)
        }
        9 => {
            let small = [1i32, 2, 3, 5, 10, 20, 50, 100];
            let n = small[idx % small.len()];
            let k = if n > 1 { (n + 1) / 2 } else { 1 };
            (n, k)
        }
        _ => {
            let n = rng.gen_range_i32(1, 1000);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, k) = pick_case(&mut rng, mode, t);
        // Sanity clamp
        let n = if n < 1 { 1 } else if n > 1000 { 1000 } else { n };
        let k = if k < 1 { 1 } else if k > n { n } else { k };
        let (nn, kk) = generate_test_case(n, k);
        println!("{{\"n\": {}, \"k\": {}}}", nn, kk);
    }
}