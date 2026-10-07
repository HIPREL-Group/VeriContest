use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1 <= n <= 5000,
    ensures
        1 <= res <= 5000,
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
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_n(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 5000,
        4 => 4999,
        5 => 4998,
        6 => rng.gen_range_i32(1, 10),
        7 => rng.gen_range_i32(1, 100),
        8 => rng.gen_range_i32(4000, 5000),
        9 => rng.gen_range_i32(1, 5000),
        10 => ((t as i32) % 5000) + 1,
        11 => {
            let base = (t as i32 * 37) % 5000;
            base + 1
        }
        _ => rng.gen_range_i32(1, 5000),
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
    let modes = 13usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_n(&mut rng, mode, t);
        let v = generate_test_case(n);
        println!("{{\"n\":{}}}", v);
    }
}