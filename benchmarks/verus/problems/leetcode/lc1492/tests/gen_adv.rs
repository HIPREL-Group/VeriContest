use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, k: i32) -> (res: (i32, i32))
    requires
        1 <= k <= n <= 1000,
    ensures
        res.0 == n,
        res.1 == k,
        1 <= res.1 <= res.0 <= 1000,
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

fn count_factors(n: i32) -> i32 {
    let mut c = 0;
    for i in 1..=n {
        if n % i == 0 {
            c += 1;
        }
    }
    c
}

fn pick_test(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1000, 1),
        2 => (1000, 1000),
        3 => {
            // prime n
            let primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                          53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
                          109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
                          173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
                          233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
                          293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359,
                          367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431,
                          433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491,
                          499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571,
                          577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641,
                          643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709,
                          719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
                          797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859,
                          863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
                          947, 953, 967, 971, 977, 983, 991, 997];
            let idx = (rng.next_u64() as usize) % primes.len();
            let n = primes[idx] as i32;
            let k = if rng.next_u64() % 2 == 0 { 1 } else { 2 };
            (n, k)
        }
        4 => {
            // perfect square
            let squares = [1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225,
                           256, 289, 324, 361, 400, 441, 484, 529, 576, 625, 676, 729,
                           784, 841, 900, 961];
            let idx = (rng.next_u64() as usize) % squares.len();
            let n: i32 = squares[idx];
            let cnt = count_factors(n);
            let k = rng.gen_range_i32(1, cnt.min(n));
            (n, k)
        }
        5 => {
            // k > number of factors (should return -1)
            let n = rng.gen_range_i32(2, 1000);
            let cnt = count_factors(n);
            if cnt < n {
                let k = rng.gen_range_i32(cnt + 1, n);
                (n, k)
            } else {
                (n, n)
            }
        }
        6 => {
            // highly composite
            let hc = [12, 24, 36, 48, 60, 120, 180, 240, 360, 720, 840];
            let idx = (rng.next_u64() as usize) % hc.len();
            let n: i32 = hc[idx];
            let cnt = count_factors(n);
            let k = rng.gen_range_i32(1, cnt);
            (n, k)
        }
        7 => {
            // k = exactly count of factors
            let n = rng.gen_range_i32(1, 1000);
            let cnt = count_factors(n);
            (n, cnt)
        }
        8 => {
            // n = k
            let n = rng.gen_range_i32(1, 1000);
            (n, n)
        }
        9 => {
            // small n
            let n = rng.gen_range_i32(1, 20);
            let k = rng.gen_range_i32(1, n);
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
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (n, k) = pick_test(&mut rng, mode);
        // sanity clamp
        let n = if n < 1 { 1 } else if n > 1000 { 1000 } else { n };
        let k = if k < 1 { 1 } else if k > n { n } else { k };
        let (rn, rk) = generate_test_case(n, k);
        println!("{{\"n\": {}, \"k\": {}}}", rn, rk);
    }
}