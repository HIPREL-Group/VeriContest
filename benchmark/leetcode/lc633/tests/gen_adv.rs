use vstd::prelude::*;

verus! {

pub fn generate_test_case(c: i32) -> (result: i32)
    requires
        0 <= c,
    ensures
        0 <= result,
        result == c,
{
    c
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    let max = i32::MAX;
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4 => 4,
        5 => 5,
        6 => {
            // Perfect square: k*k
            let k = rng.gen_range_i32(0, 46340);
            k * k
        }
        7 => {
            // Sum of two squares: a*a + b*b
            let a = rng.gen_range_i32(0, 32000);
            let b = rng.gen_range_i32(0, 32000);
            let s = a as i64 * a as i64 + b as i64 * b as i64;
            if s > max as i64 { max } else { s as i32 }
        }
        8 => max,
        9 => max - 1,
        10 => {
            // numbers of form 4^k * (8m+7) cannot be sum of two squares
            let m = rng.gen_range_i32(0, 1000);
            8 * m + 7
        }
        11 => {
            // 2^k
            let k = rng.gen_range_i32(0, 30);
            1i32 << k
        }
        12 => {
            // twice a square
            let k = rng.gen_range_i32(0, 32000);
            2 * k * k
        }
        _ => rng.gen_range_i32(0, max),
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
    let modes = 14usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let c = pick_for_mode(&mut rng, mode);
        let c = if c < 0 { 0 } else { c };
        let out = generate_test_case(c);
        println!("{{\"c\":{}}}", out);
    }
}