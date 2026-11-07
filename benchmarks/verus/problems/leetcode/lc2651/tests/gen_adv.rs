use vstd::prelude::*;

verus! {

pub fn generate_test_case(arrival: i32, delayed: i32) -> (result: (i32, i32))
    requires
        1 <= arrival < 24,
        1 <= delayed <= 24,
    ensures
        1 <= result.0 < 24,
        1 <= result.1 <= 24,
{
    (arrival, delayed)
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
        1 => (23, 24),
        2 => (23, 1),
        3 => (1, 24),
        4 => (12, 12),
        5 => (13, 11), // sum = 24 -> 0
        6 => (15, 5),
        7 => {
            // random sum == 24
            let a = rng.gen_range_i32(1, 23);
            (a, 24 - a)
        }
        8 => {
            // small arrival, large delay
            let a = rng.gen_range_i32(1, 5);
            let d = rng.gen_range_i32(20, 24);
            (a, d)
        }
        9 => {
            let a = rng.gen_range_i32(20, 23);
            let d = rng.gen_range_i32(20, 24);
            (a, d)
        }
        _ => {
            let a = rng.gen_range_i32(1, 23);
            let d = rng.gen_range_i32(1, 24);
            (a, d)
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
        let (a, d) = pick_for_mode(&mut rng, mode);
        // Safety clamp (should already be in range)
        let a = if a < 1 { 1 } else if a > 23 { 23 } else { a };
        let d = if d < 1 { 1 } else if d > 24 { 24 } else { d };
        let (arrival, delayed) = generate_test_case(a, d);
        println!("{{\"arrival_time\": {}, \"delayed_time\": {}}}", arrival, delayed);
    }
}