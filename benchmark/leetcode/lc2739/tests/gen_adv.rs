use vstd::prelude::*;

verus! {

pub fn generate_test_case(main_tank: i32, additional_tank: i32) -> (res: (i32, i32))
    ensures
        1 <= res.0 <= 100,
        1 <= res.1 <= 100,
{
    let main_tank = if main_tank < 1 { 1 } else if main_tank > 100 { 100 } else { main_tank };
    let additional_tank = if additional_tank < 1 { 1 } else if additional_tank > 100 { 100 } else { additional_tank };
    (main_tank, additional_tank)
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
        self.state = self
            .state
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
        4 => (5, 1),
        5 => (5, 0_i32.max(1)),
        6 => (4, 100),
        7 => (6, 1),
        8 => (10, 2),
        9 => (rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 10)),
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = if t < modes { t } else { (rng.next_u64() as usize) % modes };
        let (m, a) = pick(&mut rng, mode);
        let m = if m < 1 { 1 } else if m > 100 { 100 } else { m };
        let a = if a < 1 { 1 } else if a > 100 { 100 } else { a };
        let (mt, at) = generate_test_case(m, a);
        println!("{{\"main_tank\": {}, \"additional_tank\": {}}}", mt, at);
    }
}
