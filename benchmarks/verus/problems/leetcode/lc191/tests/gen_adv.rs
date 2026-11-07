use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1 <= n <= i32::MAX,
    ensures
        1 <= res <= i32::MAX,
{
    n
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn pick_value(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    let max_v: i32 = 2_147_483_647;
    match mode {
        0 => 1,
        1 => max_v,
        2 => max_v - 1,
        3 => {
            // power of 2
            let k = (t % 31) as u32;
            1i32 << k
        }
        4 => {
            // power of 2 minus 1 (all ones low)
            let k = ((t % 30) + 1) as u32;
            (1i32 << k) - 1
        }
        5 => {
            // small values
            let v = rng.gen_range_i32(1, 64);
            v
        }
        6 => {
            // alternating bit patterns
            let patterns = [
                0x55555555u32, 0x2AAAAAAAu32, 0x33333333u32, 0x0F0F0F0Fu32,
                0x00FF00FFu32, 0x0000FFFFu32, 0x7FFFFFFFu32, 0x40000000u32,
            ];
            let p = patterns[t % patterns.len()];
            (p & 0x7FFFFFFF) as i32
        }
        7 => {
            // single high bit set
            let k = ((t % 30) + 1) as u32;
            1i32 << k
        }
        8 => {
            // two bits set
            let a = (t % 31) as u32;
            let b = ((t + 7) % 31) as u32;
            let mut v: i32 = 0;
            v |= 1i32 << a;
            v |= 1i32 << b;
            if v < 1 { 1 } else { v }
        }
        9 => {
            // random in full range
            rng.gen_range_i32(1, max_v)
        }
        _ => {
            // random medium range
            rng.gen_range_i32(1, 1_000_000)
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
        let v = pick_value(&mut rng, mode, t);
        let n = generate_test_case(v);
        println!("{{\"n\":{}}}", n);
    }
}