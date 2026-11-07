use vstd::prelude::*;

verus! {

pub fn generate_test_case(x_val: i32, y_val: i32, target_val: i32) -> (res: (i32, i32, i32))
    requires
        1 <= x_val <= 1000,
        1 <= y_val <= 1000,
        1 <= target_val <= 1000,
    ensures
        1 <= res.0 <= 1000,
        1 <= res.1 <= 1000,
        1 <= res.2 <= 1000,
{
    (x_val, y_val, target_val)
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

    fn gen_i32_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn gcd(a: i32, b: i32) -> i32 {
    if b == 0 { a } else { gcd(b, a % b) }
}

fn clamp(v: i32) -> i32 {
    if v < 1 { 1 } else if v > 1000 { 1000 } else { v }
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    match mode {
        0 => {
            // classic Die Hard
            (3, 5, 4)
        }
        1 => {
            // Example 2
            (2, 6, 5)
        }
        2 => {
            // Example 3: target = x + y
            let x = rng.gen_i32_range(1, 500);
            let y = rng.gen_i32_range(1, 500);
            (x, y, x + y)
        }
        3 => {
            // target > x + y - should be false
            let x = rng.gen_i32_range(1, 400);
            let y = rng.gen_i32_range(1, 400);
            let t = clamp(x + y + rng.gen_i32_range(1, 200));
            (x, y, t)
        }
        4 => {
            // x == y
            let x = rng.gen_i32_range(1, 500);
            let t = rng.gen_i32_range(1, 1000);
            (x, x, t)
        }
        5 => {
            // x = 1, so any target <= x+y works
            let y = rng.gen_i32_range(1, 999);
            let t = rng.gen_i32_range(1, y + 1);
            (1, y, t)
        }
        6 => {
            // target = 1
            let x = rng.gen_i32_range(1, 1000);
            let y = rng.gen_i32_range(1, 1000);
            (x, y, 1)
        }
        7 => {
            // target that is multiple of gcd
            let x = rng.gen_i32_range(2, 100);
            let y = rng.gen_i32_range(2, 100);
            let g = gcd(x, y);
            let max_mul = (x + y) / g;
            let mul = rng.gen_i32_range(1, if max_mul > 0 { max_mul } else { 1 });
            let t = clamp(g * mul);
            (x, y, t)
        }
        8 => {
            // max values
            (1000, 1000, rng.gen_i32_range(1, 1000))
        }
        9 => {
            // small coprime
            let pairs = [(3, 5), (5, 7), (7, 11), (4, 9), (11, 13)];
            let idx = (rng.next_u64() as usize) % pairs.len();
            let (x, y) = pairs[idx];
            let t = rng.gen_i32_range(1, x + y);
            (x, y, t)
        }
        _ => {
            let x = rng.gen_i32_range(1, 1000);
            let y = rng.gen_i32_range(1, 1000);
            let t = rng.gen_i32_range(1, 1000);
            (x, y, t)
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
        let (x, y, target) = pick(&mut rng, mode);
        let x = clamp(x);
        let y = clamp(y);
        let target = clamp(target);
        let (rx, ry, rt) = generate_test_case(x, y, target);
        println!("{{\"x\": {}, \"y\": {}, \"target\": {}}}", rx, ry, rt);
    }
}