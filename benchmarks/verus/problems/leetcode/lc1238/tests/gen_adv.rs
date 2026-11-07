use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, start: i32) -> (result: (i32, i32))
    requires
        1 <= n <= 16,
        0 <= start,
        start < (1i32 << (n as u32)),
    ensures
        1 <= result.0 <= 16,
        0 <= result.1,
        result.1 < (1i32 << (result.0 as u32)),
        result.0 == n,
        result.1 == start,
{
    (n, start)
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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pow2(n: i32) -> i32 {
    1i32 << (n as u32)
}

fn pick_case(rng: &mut Rng, mode: usize, t: usize) -> (i32, i32) {
    match mode {
        0 => {
            // n = 1
            let n = 1;
            let s = rng.gen_range_i32(0, pow2(n) - 1);
            (n, s)
        }
        1 => {
            // small n, start=0
            let n = 1 + ((t as i32) % 5);
            (n, 0)
        }
        2 => {
            // small n, start = 2^n - 1
            let n = 1 + ((t as i32) % 5);
            (n, pow2(n) - 1)
        }
        3 => {
            // n = 16, start = 0
            (16, 0)
        }
        4 => {
            // n = 16, start = 2^16 - 1
            (16, 65535)
        }
        5 => {
            // n = 16, random start
            let s = rng.gen_range_i32(0, 65535);
            (16, s)
        }
        6 => {
            // mid n
            let n = 8;
            let s = rng.gen_range_i32(0, pow2(n) - 1);
            (n, s)
        }
        7 => {
            // n = 2, all starts
            let n = 2;
            let s = (t as i32) % 4;
            (n, s)
        }
        8 => {
            // n=3
            let n = 3;
            let s = (t as i32) % 8;
            (n, s)
        }
        9 => {
            // random n and start
            let n = rng.gen_range_i32(1, 16);
            let s = rng.gen_range_i32(0, pow2(n) - 1);
            (n, s)
        }
        _ => {
            // power of 2 starts
            let n = rng.gen_range_i32(2, 16);
            let bit = rng.gen_range_i32(0, n - 1);
            let s = 1i32 << (bit as u32);
            (n, s)
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
        let (n, start) = pick_case(&mut rng, mode, t);
        // Call the verified generator to ensure preconditions hold.
        let (nn, ss) = generate_test_case(n, start);
        println!("{{\"n\": {}, \"start\": {}}}", nn, ss);
    }
}