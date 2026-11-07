use vstd::prelude::*;

verus! {

pub fn generate_test_case(base: i32, offset: i32) -> (k: i32)
    requires
        1 <= base <= 100_000,
        0 <= offset,
        base as int + offset as int <= 100_000,
    ensures
        1 <= k <= 100_000,
{
    let k = base + offset;
    assert(1 <= k);
    assert(k <= 100_000);
    k
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }

    fn gen_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 1
    }
}

fn gcd_i32(mut a: i32, mut b: i32) -> i32 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    if a < 0 { -a } else { a }
}

fn pow_mod(mut a: i32, mut e: i32, m: i32) -> i32 {
    let mut r: i64 = 1;
    let mut base: i64 = (a % m) as i64;
    let modu = m as i64;
    while e > 0 {
        if (e & 1) == 1 {
            r = (r * base) % modu;
        }
        base = (base * base) % modu;
        e >>= 1;
    }
    r as i32
}

fn is_prime(n: i32) -> bool {
    if n < 2 {
        return false;
    }
    if n % 2 == 0 {
        return n == 2;
    }
    let mut d = 3i32;
    while (d as i64) * (d as i64) <= n as i64 {
        if n % d == 0 {
            return false;
        }
        d += 2;
    }
    true
}

fn next_prime_at_least(mut x: i32) -> i32 {
    if x <= 2 {
        return 2;
    }
    if x % 2 == 0 {
        x += 1;
    }
    while !is_prime(x) {
        x += 2;
    }
    x
}

fn largest_power_leq(base: i32, limit: i32) -> i32 {
    let mut v: i64 = 1;
    while v * base as i64 <= limit as i64 {
        v *= base as i64;
    }
    v as i32
}

fn mode_value(rng: &mut Rng, mode: usize, idx: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 100_000,
        2 => {
            let vals = [2, 4, 5, 8, 10, 20, 25, 40, 50, 80];
            vals[idx % vals.len()]
        }
        3 => {
            let vals = [3, 7, 9, 11, 13, 27, 37, 41, 99, 99999];
            vals[idx % vals.len()]
        }
        4 => {
            let vals = [99991, 99989, 99971, 99961, 99929, 99923];
            vals[idx % vals.len()]
        }
        5 => {
            let vals = [99990, 99995, 99996, 99998, 99994, 99992];
            vals[idx % vals.len()]
        }
        6 => {
            let p = next_prime_at_least(90000 + (idx as i32 * 137) % 9000);
            let mut k = p;
            if k > 100_000 {
                k = 99991;
            }
            k
        }
        7 => {
            let choices = [3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049];
            choices[idx % choices.len()]
        }
        8 => {
            let choices = [7, 49, 343, 2401, 16807];
            choices[idx % choices.len()]
        }
        9 => {
            let base = rng.gen_range_i32(1, 100_000);
            let mut k = base;
            while gcd_i32(k, 10) != 1 {
                k = if k == 100_000 { 99_999 } else { k + 1 };
            }
            k
        }
        10 => {
            let base = rng.gen_range_i32(1, 100_000);
            let mut k = base;
            while k % 2 != 0 && k % 5 != 0 {
                k = if k == 100_000 { 100_000 } else { k + 1 };
                if k > 100_000 {
                    k = 100_000;
                    break;
                }
            }
            k
        }
        11 => {
            let mut k = rng.gen_range_i32(1, 100_000);
            if rng.gen_bool() {
                k = largest_power_leq(2, 100_000).min(k.max(1));
            } else {
                k = largest_power_leq(5, 100_000).min(k.max(1));
            }
            if k < 1 { 1 } else { k }
        }
        12 => {
            let p = next_prime_at_least(30000 + (idx as i32 * 97) % 20000);
            let mut k = p;
            if k != 2 && k != 5 {
                let ord_hint = pow_mod(10, (p - 1) / 2, p);
                if ord_hint == 1 {
                    k = p;
                }
            }
            if k > 100_000 { 99991 } else { k }
        }
        _ => rng.gen_range_i32(1, 100_000),
    }
}

fn main() {
    use std::env;
    use std::io::{self, Write};

    let seed = env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());

    let total: usize = 220;
    let modes: usize = 13;

    for i in 0..total {
        let mode = i % modes;
        let raw = mode_value(&mut rng, mode, i / modes);

        let (base, offset) = if raw <= 50_000 {
            (raw, 0)
        } else {
            (50_000, raw - 50_000)
        };

        let k = generate_test_case(base, offset);
        writeln!(out, "{{\"k\": {}}}", k).unwrap();
    }
}