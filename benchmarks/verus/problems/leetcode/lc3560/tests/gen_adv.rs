use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, m: i32, k: i32) -> (result: (i32, i32, i32))
    requires
        2 <= k <= 100_000,
        1 <= n <= 2 * k,
        1 <= m <= 2 * k,
        n <= k || m <= k,
    ensures
        ({
            let (nn, mm, kk) = result;
            &&& 2 <= kk <= 100_000
            &&& 1 <= nn <= 2 * kk
            &&& 1 <= mm <= 2 * kk
            &&& (nn <= kk || mm <= kk)
        }),
{
    (n, m, k)
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

fn build_case(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    match mode {
        0 => {
            // smallest k
            let k = 2i32;
            let n = rng.gen_range_i32(1, 2 * k);
            let m = rng.gen_range_i32(1, 2 * k);
            let (n, m) = if n > k && m > k {
                if rng.next_u64() % 2 == 0 { (k, m) } else { (n, k) }
            } else { (n, m) };
            (n, m, k)
        }
        1 => {
            // largest k
            let k = 100_000i32;
            let n = rng.gen_range_i32(1, 2 * k);
            let m = rng.gen_range_i32(1, 2 * k);
            let (n, m) = if n > k && m > k {
                if rng.next_u64() % 2 == 0 { (k, m) } else { (n, k) }
            } else { (n, m) };
            (n, m, k)
        }
        2 => {
            // both fit exactly (no cut)
            let k = rng.gen_range_i32(2, 100_000);
            let n = rng.gen_range_i32(1, k);
            let m = rng.gen_range_i32(1, k);
            (n, m, k)
        }
        3 => {
            // n = 2k, m small
            let k = rng.gen_range_i32(2, 100_000);
            let n = 2 * k;
            let m = rng.gen_range_i32(1, k);
            (n, m, k)
        }
        4 => {
            // m = 2k, n small
            let k = rng.gen_range_i32(2, 100_000);
            let m = 2 * k;
            let n = rng.gen_range_i32(1, k);
            (n, m, k)
        }
        5 => {
            // n = k+1, m = k
            let k = rng.gen_range_i32(2, 100_000);
            let n = k + 1;
            let m = k;
            (n, m, k)
        }
        6 => {
            // n = k, m = k+1
            let k = rng.gen_range_i32(2, 100_000);
            let n = k;
            let m = k + 1;
            (n, m, k)
        }
        7 => {
            // n = k, m = k
            let k = rng.gen_range_i32(2, 100_000);
            (k, k, k)
        }
        8 => {
            // n = 1, m = 1
            let k = rng.gen_range_i32(2, 100_000);
            (1, 1, k)
        }
        9 => {
            // large n just over k
            let k = rng.gen_range_i32(2, 100_000);
            let n = rng.gen_range_i32(k + 1, 2 * k);
            let m = rng.gen_range_i32(1, k);
            (n, m, k)
        }
        _ => {
            // random general
            let k = rng.gen_range_i32(2, 100_000);
            let n = rng.gen_range_i32(1, 2 * k);
            let m = rng.gen_range_i32(1, 2 * k);
            // ensure n <= k || m <= k
            let (n, m) = if n > k && m > k {
                if rng.next_u64() % 2 == 0 { (k, m) } else { (n, k) }
            } else { (n, m) };
            (n, m, k)
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
        let (n, m, k) = build_case(&mut rng, mode);
        let (n, m, k) = generate_test_case(n, m, k);
        println!("{{\"n\": {}, \"m\": {}, \"k\": {}}}", n, m, k);
    }
}