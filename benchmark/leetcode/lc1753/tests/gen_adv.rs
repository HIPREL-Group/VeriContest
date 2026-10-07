use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i32, b: i32, c: i32) -> (res: (i32, i32, i32))
    requires
        1 <= a <= 100_000,
        1 <= b <= 100_000,
        1 <= c <= 100_000,
    ensures
        1 <= res.0 <= 100_000,
        1 <= res.1 <= 100_000,
        1 <= res.2 <= 100_000,
        res.0 == a,
        res.1 == b,
        res.2 == c,
{
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
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn clamp_val(v: i32) -> i32 {
    if v < 1 { 1 } else if v > 100_000 { 100_000 } else { v }
}

fn pick(mode: usize, rng: &mut Rng) -> (i32, i32, i32) {
    match mode {
        0 => (1, 1, 1),
        1 => (100_000, 100_000, 100_000),
        2 => (1, 1, 100_000),
        3 => (1, 100_000, 100_000),
        4 => (100_000, 1, 1),
        5 => {
            // a + b == c exactly (sum equal to max)
            let a = rng.gen_i32(1, 50_000);
            let b = rng.gen_i32(1, 50_000);
            let c = a + b;
            (a, b, clamp_val(c))
        }
        6 => {
            // a + b < c (one pile dominates)
            let a = rng.gen_i32(1, 100);
            let b = rng.gen_i32(1, 100);
            let c = rng.gen_i32(1000, 100_000);
            (a, b, c)
        }
        7 => {
            // all equal
            let x = rng.gen_i32(1, 100_000);
            (x, x, x)
        }
        8 => {
            // two equal, one different
            let x = rng.gen_i32(1, 100_000);
            let y = rng.gen_i32(1, 100_000);
            (x, x, y)
        }
        9 => {
            // small random
            (rng.gen_i32(1, 20), rng.gen_i32(1, 20), rng.gen_i32(1, 20))
        }
        _ => {
            (rng.gen_i32(1, 100_000), rng.gen_i32(1, 100_000), rng.gen_i32(1, 100_000))
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
    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (a0, b0, c0) = pick(mode, &mut rng);
        let a = clamp_val(a0);
        let b = clamp_val(b0);
        let c = clamp_val(c0);
        let (ra, rb, rc) = generate_test_case(a, b, c);
        println!("{{\"a\": {}, \"b\": {}, \"c\": {}}}", ra, rb, rc);
    }
}