use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i32, b: i32) -> (result: (i32, i32))
    requires
        1 <= a <= 1000,
        1 <= b <= 1000,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= 1000,
{
    (a, b)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1000, 1000),
        2 => (1, 1000),
        3 => (1000, 1),
        4 => {
            let v = rng.gen_range_i32(1, 1000);
            (v, v)
        }
        5 => {
            let p = [2i32, 3, 5, 7, 11, 13, 17, 19, 23];
            let a = p[(rng.next_u64() as usize) % p.len()];
            let b = p[(rng.next_u64() as usize) % p.len()];
            (a, b)
        }
        6 => {
            let a = rng.gen_range_i32(1, 1000);
            (a, 1)
        }
        7 => {
            let b = rng.gen_range_i32(1, 1000);
            (1, b)
        }
        8 => {
            // highly composite
            let opts = [12i32, 24, 36, 48, 60, 72, 120, 180, 240, 360, 720, 840];
            let a = opts[(rng.next_u64() as usize) % opts.len()];
            let b = opts[(rng.next_u64() as usize) % opts.len()];
            (a, b)
        }
        9 => {
            // one is multiple of other
            let a = rng.gen_range_i32(1, 31);
            let k = rng.gen_range_i32(1, 1000 / a.max(1));
            (a, a * k)
        }
        _ => {
            let a = rng.gen_range_i32(1, 1000);
            let b = rng.gen_range_i32(1, 1000);
            (a, b)
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (a, b) = pick_for_mode(&mut rng, mode);
        let (a, b) = generate_test_case(a, b);
        println!("{{\"a\": {}, \"b\": {}}}", a, b);
    }
}