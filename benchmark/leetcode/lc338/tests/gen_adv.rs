use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        0 <= n <= 100000,
    ensures
        0 <= res <= 100000,
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 100000,
        4 => 99999,
        5 => {
            // powers of two
            let p = (t % 17) as u32;
            1i32 << p
        }
        6 => {
            // power of two minus 1
            let p = (t % 17) as u32;
            (1i32 << p) - 1
        }
        7 => rng.gen_range_i32(0, 100),
        8 => rng.gen_range_i32(100, 10000),
        9 => rng.gen_range_i32(10000, 100000),
        _ => rng.gen_range_i32(0, 100000),
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
        let mut n = pick_for_mode(&mut rng, mode, t);
        if n < 0 {
            n = 0;
        }
        if n > 100000 {
            n = 100000;
        }
        let out = generate_test_case(n);
        println!("{{\"n\":{}}}", out);
    }
}