use vstd::prelude::*;

verus! {

pub fn generate_test_case(steps: i32, arr_len: i32) -> (result: (i32, i32))
    requires
        1 <= steps <= 500,
        1 <= arr_len <= 1_000_000,
    ensures
        1 <= result.0 <= 500,
        1 <= result.1 <= 1_000_000,
        result.0 == steps,
        result.1 == arr_len,
{
    (steps, arr_len)
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1, 1_000_000),
        2 => (500, 1),
        3 => (500, 1_000_000),
        4 => (500, 500),
        5 => (500, 250),
        6 => (rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 10)),
        7 => (rng.gen_range_i32(1, 500), 1),
        8 => (1, rng.gen_range_i32(1, 1_000_000)),
        9 => {
            let s = rng.gen_range_i32(1, 500);
            (s, s / 2 + 1)
        }
        10 => {
            let s = rng.gen_range_i32(1, 500);
            (s, rng.gen_range_i32(1, 1_000_000))
        }
        11 => (2, 2),
        12 => (3, 2),
        13 => (4, 2),
        14 => (500, 2),
        _ => (rng.gen_range_i32(1, 500), rng.gen_range_i32(1, 1_000_000)),
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (steps, arr_len) = pick_for_mode(&mut rng, mode);
        let (s, a) = generate_test_case(steps, arr_len);
        println!("{{\"steps\": {}, \"arr_len\": {}}}", s, a);
    }
}