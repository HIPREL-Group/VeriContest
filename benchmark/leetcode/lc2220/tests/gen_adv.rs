use vstd::prelude::*;

verus! {

pub fn generate_test_case(start: i32, goal: i32) -> (res: (i32, i32))
    ensures
        0 <= res.0 <= 1000000000,
        0 <= res.1 <= 1000000000,
{
    let start = if start < 0 { 0 } else if start > 1000000000 { 1000000000 } else { start };
    let goal = if goal < 0 { 0 } else if goal > 1000000000 { 1000000000 } else { goal };
    (start, goal)
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

    fn gen_i32_range(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    let max = 1_000_000_000i32;
    match mode {
        0 => (0, 0),
        1 => {
            let v = rng.gen_i32_range(0, max);
            (v, v)
        }
        2 => (0, rng.gen_i32_range(0, max)),
        3 => (rng.gen_i32_range(0, max), 0),
        4 => (max, 0),
        5 => (0, max),
        6 => (max, max),
        7 => {
            // powers of 2
            let a = 1i32 << rng.gen_i32_range(0, 30);
            let b = 1i32 << rng.gen_i32_range(0, 30);
            (a, b)
        }
        8 => {
            // all ones up to some bit vs zero
            let bits = rng.gen_i32_range(1, 30);
            let v = (1i32 << bits) - 1;
            (v, 0)
        }
        9 => {
            // small numbers
            (rng.gen_i32_range(0, 31), rng.gen_i32_range(0, 31))
        }
        10 => {
            // complementary-ish
            let a = rng.gen_i32_range(0, max);
            let b = a ^ rng.gen_i32_range(0, max);
            (a, b.max(0))
        }
        _ => {
            (rng.gen_i32_range(0, max), rng.gen_i32_range(0, max))
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
        let (s, g) = pick_for_mode(&mut rng, mode);
        let (start, goal) = generate_test_case(s, g);
        println!("{{\"start\":{},\"goal\":{}}}", start, goal);
    }
}
