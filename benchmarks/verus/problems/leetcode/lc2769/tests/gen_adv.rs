use vstd::prelude::*;

verus! {

pub fn generate_test_case(num: i32, t: i32) -> (result: (i32, i32))
    requires
        1 <= num <= 50,
        1 <= t <= 50,
    ensures
        1 <= result.0 <= 50,
        1 <= result.1 <= 50,
{
    (num, t)
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
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (50, 50),
        2 => (1, 50),
        3 => (50, 1),
        4 => (rng.gen_range_i32(1, 50), 1),
        5 => (1, rng.gen_range_i32(1, 50)),
        6 => (rng.gen_range_i32(1, 50), 50),
        7 => (50, rng.gen_range_i32(1, 50)),
        8 => (25, 25),
        9 => (rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 10)),
        _ => (rng.gen_range_i32(1, 50), rng.gen_range_i32(1, 50)),
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

    for i in 0..total {
        let mode = i % modes;
        let (num, t) = pick_for_mode(&mut rng, mode);
        let (out_num, out_t) = generate_test_case(num, t);
        println!("{{\"num\": {}, \"t\": {}}}", out_num, out_t);
    }
}