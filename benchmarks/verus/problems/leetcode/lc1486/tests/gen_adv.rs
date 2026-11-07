use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, start: i32) -> (result: (i32, i32))
    requires
        1 <= n <= 1000,
        0 <= start <= 1000,
    ensures
        1 <= result.0 <= 1000,
        0 <= result.1 <= 1000,
{
    (n, start)
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
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 0),
        1 => (1, 1000),
        2 => (1000, 0),
        3 => (1000, 1000),
        4 => (5, 0),
        5 => (4, 3),
        6 => (rng.gen_range_i32(1, 10), rng.gen_range_i32(0, 10)),
        7 => (rng.gen_range_i32(990, 1000), rng.gen_range_i32(990, 1000)),
        8 => (rng.gen_range_i32(1, 1000), 0),
        9 => (rng.gen_range_i32(1, 1000), rng.gen_range_i32(0, 1000)),
        _ => (rng.gen_range_i32(1, 1000), rng.gen_range_i32(0, 1000)),
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, start) = pick(&mut rng, mode);
        let (nn, ss) = generate_test_case(n, start);
        println!("{{\"n\": {}, \"start\": {}}}", nn, ss);
    }
}