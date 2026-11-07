use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i64, hi_val: i64, lo_choice: bool) -> (r: (i64, i64, i64))
    requires
        2 <= n <= 100_000,
        1 <= hi_val < n,
        (n - 1) as int % hi_val as int == 0,
    ensures
        ({
            let (rn, rx, ry) = r;
            &&& rn == n
            &&& 0 <= rx < rn
            &&& 0 <= ry < rn
            &&& 2 <= rn <= 100_000
            &&& {
                let lo = if rx < ry { rx as int } else { ry as int };
                let hi = if rx > ry { rx as int } else { ry as int };
                lo == 0 && hi > 0 && (rn - 1) as int % hi == 0
            }
        }),
{
    if lo_choice {
        // x = 0, y = hi_val
        (n, 0i64, hi_val)
    } else {
        // x = hi_val, y = 0
        (n, hi_val, 0i64)
    }
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
    fn gen_bool(&mut self) -> bool {
        self.next_u64() % 2 == 0
    }
}

fn divisors_of(m: i64) -> Vec<i64> {
    // returns all divisors d >= 1 of m
    let mut res = Vec::new();
    let mut d: i64 = 1;
    while d * d <= m {
        if m % d == 0 {
            res.push(d);
            if d != m / d {
                res.push(m / d);
            }
        }
        d += 1;
    }
    res
}

fn pick_test(rng: &mut Rng, mode: usize) -> (i64, i64, bool) {
    // returns (n, hi_val, lo_choice)
    match mode {
        0 => {
            // n=2, hi=1
            (2, 1, rng.gen_bool())
        }
        1 => {
            // n=3, hi=2
            (3, 2, rng.gen_bool())
        }
        2 => {
            // n where n-1 is prime, hi = n-1
            let n = 100_000i64;
            (n, n - 1, rng.gen_bool())
        }
        3 => {
            // hi = 1 (n-1 divisible by 1 always)
            let n = rng.gen_range_i64(2, 100_000);
            (n, 1, rng.gen_bool())
        }
        4 => {
            // n-1 = power of 2
            let exps = [1i64, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536];
            let idx = (rng.next_u64() as usize) % exps.len();
            let m = exps[idx];
            let n = m + 1;
            let divs = divisors_of(m);
            let d = divs[(rng.next_u64() as usize) % divs.len()];
            if d >= 1 && d < n {
                (n, d, rng.gen_bool())
            } else {
                (n, 1, rng.gen_bool())
            }
        }
        5 => {
            // random n, pick random divisor of n-1
            let n = rng.gen_range_i64(2, 100_000);
            let m = n - 1;
            let divs = divisors_of(m);
            let d = divs[(rng.next_u64() as usize) % divs.len()];
            if d >= 1 && d < n {
                (n, d, rng.gen_bool())
            } else {
                (n, 1, rng.gen_bool())
            }
        }
        6 => {
            // highly composite-ish: n-1 = 60, 120, 360...
            let options = [61i64, 121, 361, 841, 2521, 5041, 10081, 55441];
            let n = options[(rng.next_u64() as usize) % options.len()];
            let m = n - 1;
            let divs = divisors_of(m);
            let d = divs[(rng.next_u64() as usize) % divs.len()];
            if d >= 1 && d < n {
                (n, d, rng.gen_bool())
            } else {
                (n, 1, rng.gen_bool())
            }
        }
        7 => {
            // n=2
            (2, 1, false)
        }
        8 => {
            // large n, hi = n-1
            let n = rng.gen_range_i64(1000, 100_000);
            (n, n - 1, rng.gen_bool())
        }
        9 => {
            // hi = (n-1)/2 when even
            let mut n = rng.gen_range_i64(3, 100_000);
            if (n - 1) % 2 != 0 {
                n += 1;
            }
            if n > 100_000 { n = 100_000; if (n-1) % 2 != 0 { n = 99_999; } }
            let hi = (n - 1) / 2;
            if hi >= 1 && hi < n {
                (n, hi, rng.gen_bool())
            } else {
                (n, 1, rng.gen_bool())
            }
        }
        _ => {
            let n = rng.gen_range_i64(2, 100_000);
            let divs = divisors_of(n - 1);
            let d = divs[(rng.next_u64() as usize) % divs.len()];
            if d >= 1 && d < n {
                (n, d, rng.gen_bool())
            } else {
                (n, 1, rng.gen_bool())
            }
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
        let (n, hi_val, lo_choice) = pick_test(&mut rng, mode);
        // Sanity: ensure preconditions for generate_test_case
        if !(2 <= n && n <= 100_000) { continue; }
        if !(1 <= hi_val && hi_val < n) { continue; }
        if (n - 1) % hi_val != 0 { continue; }
        let (rn, rx, ry) = generate_test_case(n, hi_val, lo_choice);
        println!("{{\"n\": {}, \"x\": {}, \"y\": {}}}", rn, rx, ry);
    }
}