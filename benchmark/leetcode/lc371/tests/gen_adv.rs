use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32) -> (res: i32)
    requires
        -1000 <= x <= 1000,
    ensures
        -1000 <= res <= 1000,
{
    x
}

pub fn generate_pair(a: i32, b: i32) -> (res: (i32, i32))
    requires
        -1000 <= a <= 1000,
        -1000 <= b <= 1000,
    ensures
        -1000 <= res.0 <= 1000,
        -1000 <= res.1 <= 1000,
{
    (a, b)
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
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (0, 0),
        1 => (1000, 1000),
        2 => (-1000, -1000),
        3 => (1000, -1000),
        4 => (-1000, 1000),
        5 => {
            let a = rng.gen_range_i32(-1000, 1000);
            (a, -a)
        }
        6 => {
            let a = rng.gen_range_i32(-1000, 1000);
            (a, 0)
        }
        7 => {
            let b = rng.gen_range_i32(-1000, 1000);
            (0, b)
        }
        8 => {
            let a = rng.gen_range_i32(500, 1000);
            let b = rng.gen_range_i32(500, 1000);
            (a, b)
        }
        9 => {
            let a = rng.gen_range_i32(-1000, -500);
            let b = rng.gen_range_i32(-1000, -500);
            (a, b)
        }
        _ => {
            let a = rng.gen_range_i32(-1000, 1000);
            let b = rng.gen_range_i32(-1000, 1000);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (a, b) = pick(&mut rng, mode);
        let (va, vb) = generate_pair(a, b);
        println!("{{\"a\": {}, \"b\": {}}}", va, vb);
    }
}