use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i32, b: i32, c: i32) -> (result: (i32, i32, i32))
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.2 <= 1_000_000_000,
{
    let a = if a < 1 { 1 } else if a > 1000000000 { 1000000000 } else { a };
    let b = if b < 1 { 1 } else if b > 1000000000 { 1000000000 } else { b };
    let c = if c < 1 { 1 } else if c > 1000000000 { 1000000000 } else { c };
    (a, b, c)
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
        lo + (self.next_u64() % span) as i32
    }
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    let max = 1_000_000_000i32;
    match mode {
        0 => {
            // small numbers
            let a = rng.gen_range_i32(1, 20);
            let b = rng.gen_range_i32(1, 20);
            let c = rng.gen_range_i32(1, 20);
            (a, b, c)
        }
        1 => {
            // a | b == c already
            let a = rng.gen_range_i32(1, max);
            let b = rng.gen_range_i32(1, max);
            let c_raw = a | b;
            let c = if c_raw < 1 { 1 } else { c_raw };
            (a, b, c)
        }
        2 => {
            // c is 1 (boundary)
            let a = rng.gen_range_i32(1, max);
            let b = rng.gen_range_i32(1, max);
            (a, b, 1)
        }
        3 => {
            // a, b are 1
            let c = rng.gen_range_i32(1, max);
            (1, 1, c)
        }
        4 => {
            // all max
            (max, max, max)
        }
        5 => {
            // c = max, a,b small
            (1, 1, max)
        }
        6 => {
            // power of two values
            let pa = rng.gen_range_i32(0, 29);
            let pb = rng.gen_range_i32(0, 29);
            let pc = rng.gen_range_i32(0, 29);
            let a = 1i32 << pa;
            let b = 1i32 << pb;
            let c = 1i32 << pc;
            let a = if a < 1 || a > max { 1 } else { a };
            let b = if b < 1 || b > max { 1 } else { b };
            let c = if c < 1 || c > max { 1 } else { c };
            (a, b, c)
        }
        7 => {
            // a == b == c
            let v = rng.gen_range_i32(1, max);
            (v, v, v)
        }
        8 => {
            // c = 0 not allowed since c>=1, use c with single bit
            let a = rng.gen_range_i32(1, max);
            let b = rng.gen_range_i32(1, max);
            (a, b, 1)
        }
        9 => {
            // examples
            match rng.next_u64() % 3 {
                0 => (2, 6, 5),
                1 => (4, 2, 7),
                _ => (1, 2, 3),
            }
        }
        _ => {
            let a = rng.gen_range_i32(1, max);
            let b = rng.gen_range_i32(1, max);
            let c = rng.gen_range_i32(1, max);
            (a, b, c)
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
        let (a, b, c) = pick(&mut rng, mode);
        let (a, b, c) = generate_test_case(a, b, c);
        println!("{{\"a\": {}, \"b\": {}, \"c\": {}}}", a, b, c);
    }
}
