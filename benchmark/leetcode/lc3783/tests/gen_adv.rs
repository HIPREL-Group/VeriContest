use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1 <= n <= 1_000_000_000,
    ensures
        1 <= res <= 1_000_000_000,
{
    n
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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

fn pick_value(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 1_000_000_000,
        2 => rng.gen_range_i32(1, 9),
        3 => rng.gen_range_i32(10, 99),
        4 => rng.gen_range_i32(100, 999),
        5 => {
            // palindrome-like: digits all same
            let d = rng.gen_range_i32(1, 9);
            let len = rng.gen_range_i32(1, 9) as usize;
            let mut v: i64 = 0;
            for _ in 0..len {
                v = v * 10 + d as i64;
            }
            if v > 1_000_000_000 { 1_000_000_000 } else { v as i32 }
        }
        6 => {
            // trailing zeros
            let base = rng.gen_range_i32(1, 9999);
            let zeros = rng.gen_range_i32(0, 5);
            let mut v: i64 = base as i64;
            for _ in 0..zeros {
                v *= 10;
            }
            if v > 1_000_000_000 || v < 1 { 10 } else { v as i32 }
        }
        7 => {
            // power of 10
            let p = rng.gen_range_i32(0, 9);
            let mut v: i64 = 1;
            for _ in 0..p {
                v *= 10;
            }
            v as i32
        }
        8 => {
            // 9s
            let len = rng.gen_range_i32(1, 9) as usize;
            let mut v: i64 = 0;
            for _ in 0..len {
                v = v * 10 + 9;
            }
            if v > 1_000_000_000 { 999_999_999 } else { v as i32 }
        }
        9 => {
            // palindrome number
            let half = rng.gen_range_i32(1, 99999);
            let mut rev = 0i64;
            let mut t = half as i64;
            while t > 0 {
                rev = rev * 10 + t % 10;
                t /= 10;
            }
            let mut v: i64 = half as i64;
            let mut r = rev;
            while r > 0 {
                v = v * 10 + r % 10;
                r /= 10;
            }
            if v < 1 || v > 1_000_000_000 { 121 } else { v as i32 }
        }
        _ => rng.gen_range_i32(1, 1_000_000_000),
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let mut v = pick_value(&mut rng, mode);
        if v < 1 {
            v = 1;
        }
        if v > 1_000_000_000 {
            v = 1_000_000_000;
        }
        let res = generate_test_case(v);
        println!("{{\"n\": {}}}", res);
    }
}