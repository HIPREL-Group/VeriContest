use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, k: i32) -> (res: (i32, i32))
    requires
        0 <= n <= 50,
        1 <= k <= 100000,
    ensures
        0 <= res.0 <= 50,
        1 <= res.1 <= 100000,
        res.0 == n,
        res.1 == k,
{
    (n, k)
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
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

// For small n, paint_ways grows slowly with k. Let's calculate safe k for a given n.
// paint_ways(n, k) = (k-1) * (paint_ways(n-1, k) + paint_ways(n-2, k))
// For n=50 and k=2, result is manageable but for k large it overflows i32::MAX.
// To be safe, let's only generate (n, k) where paint_ways fits in i32.
// For n <= 2, always fits. For n >= 3, we need to be careful.
// Let's compute and clamp k.

fn paint_ways_capped(n: i32, k: i32) -> i64 {
    // returns min(actual, i64::MAX/2) to detect overflow
    let cap: i64 = i32::MAX as i64;
    if n <= 0 {
        0
    } else if n == 1 {
        k as i64
    } else if n == 2 {
        (k as i64) * (k as i64)
    } else {
        let mut a: i64 = k as i64;           // paint_ways(1)
        let mut b: i64 = (k as i64) * (k as i64); // paint_ways(2)
        let km1: i64 = (k - 1) as i64;
        let mut i = 3;
        while i <= n {
            // new = (k-1) * (a + b), but guard against overflow
            let sum = a.saturating_add(b);
            let new_val = km1.saturating_mul(sum);
            a = b;
            b = new_val;
            if b > cap {
                return cap + 1;
            }
            i += 1;
        }
        b
    }
}

fn find_max_k_for_n(n: i32) -> i32 {
    // Binary search for largest k in [1, 100000] such that paint_ways fits in i32.
    if n <= 2 {
        if n == 2 {
            // k*k <= i32::MAX => k <= ~46340
            return 46340;
        }
        return 100000;
    }
    let mut lo: i32 = 1;
    let mut hi: i32 = 100000;
    let mut best: i32 = 1;
    while lo <= hi {
        let mid = lo + (hi - lo) / 2;
        let v = paint_ways_capped(n, mid);
        if v <= i32::MAX as i64 {
            best = mid;
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }
    best
}

fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (0, rng.gen_range_i32(1, 100000)),
        1 => (1, rng.gen_range_i32(1, 100000)),
        2 => (2, rng.gen_range_i32(1, 46340)),
        3 => {
            let n = 3;
            let k_max = find_max_k_for_n(n);
            (n, rng.gen_range_i32(1, k_max))
        }
        4 => {
            let n = rng.gen_range_i32(4, 10);
            let k_max = find_max_k_for_n(n);
            (n, rng.gen_range_i32(1, k_max))
        }
        5 => {
            let n = rng.gen_range_i32(10, 30);
            let k_max = find_max_k_for_n(n);
            (n, rng.gen_range_i32(1, k_max))
        }
        6 => {
            let n = rng.gen_range_i32(30, 50);
            let k_max = find_max_k_for_n(n);
            (n, rng.gen_range_i32(1, k_max))
        }
        7 => {
            let n = 50;
            let k_max = find_max_k_for_n(n);
            (n, k_max)
        }
        8 => {
            // k = 1 special case
            let n = rng.gen_range_i32(0, 50);
            (n, 1)
        }
        9 => {
            // k = 2 special case
            let n = rng.gen_range_i32(0, 50);
            let k_max = find_max_k_for_n(n);
            let k = if 2 <= k_max { 2 } else { k_max };
            (n, k)
        }
        _ => {
            let n = rng.gen_range_i32(0, 50);
            let k_max = find_max_k_for_n(n);
            (n, rng.gen_range_i32(1, k_max))
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
        let (n, k) = pick_case(&mut rng, mode);
        let (nn, kk) = generate_test_case(n, k);
        println!("{{\"n\": {}, \"k\": {}}}", nn, kk);
    }
}