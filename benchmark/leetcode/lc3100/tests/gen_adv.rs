use vstd::prelude::*;

verus! {

pub fn generate_test_case(nb: i32, ne: i32) -> (result: (i32, i32))
    requires
        1 <= nb <= 100,
        1 <= ne <= 100,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
{
    (nb, ne)
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

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1, 100),
        2 => (100, 1),
        3 => (100, 100),
        4 => (rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 10)),
        5 => (rng.gen_range_i32(1, 100), 1),
        6 => (rng.gen_range_i32(1, 100), 2),
        7 => (13, 6),
        8 => (10, 3),
        9 => (rng.gen_range_i32(90, 100), rng.gen_range_i32(1, 5)),
        _ => (rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100)),
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
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (nb, ne) = pick(&mut rng, mode);
        let (a, b) = generate_test_case(nb, ne);
        println!("{{\"num_bottles\": {}, \"num_exchange\": {}}}", a, b);
    }
}