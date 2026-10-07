use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, t: i32) -> (result: (i32, i32))
    requires
        1 <= n <= 100,
        1 <= t <= 10,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 10,
{
    (n, t)
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

fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1, 10),
        2 => (100, 1),
        3 => (100, 10),
        4 => (10, 2),
        5 => (15, 3),
        6 => (rng.gen_range_i32(1, 9), rng.gen_range_i32(1, 10)),
        7 => (rng.gen_range_i32(10, 99), rng.gen_range_i32(1, 10)),
        8 => (rng.gen_range_i32(90, 100), rng.gen_range_i32(1, 10)),
        9 => {
            // likely to require crossing to next decade
            let n = rng.gen_range_i32(1, 100);
            (n, 7)
        }
        10 => {
            let n = rng.gen_range_i32(1, 100);
            (n, 9)
        }
        11 => (99, 7),
        12 => (89, 7),
        13 => (rng.gen_range_i32(1, 100), 10),
        14 => (rng.gen_range_i32(1, 100), 1),
        _ => (rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 10)),
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
    let modes = 16usize;
    let total = 200usize;

    for i in 0..total {
        let mode = i % modes;
        let (n, t) = pick_case(&mut rng, mode);
        let (nn, tt) = generate_test_case(n, t);
        println!("{{\"n\":{},\"t\":{}}}", nn, tt);
    }
}