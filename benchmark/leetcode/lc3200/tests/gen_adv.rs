use vstd::prelude::*;

verus! {

pub fn generate_test_case(red: i32, blue: i32, row: i32, red_turn: bool) -> (result: (i32, i32, i32, bool))
    requires
        1 <= red <= 100,
        1 <= blue <= 100,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
        result.0 == red,
        result.1 == blue,
        result.2 == row,
        result.3 == red_turn,
{
    (red, blue, row, red_turn)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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

    fn gen_bool(&mut self) -> bool {
        self.next_u64() % 2 == 0
    }
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32, i32, bool) {
    match mode {
        0 => (1, 1, 1, true),
        1 => (1, 1, 1, false),
        2 => (100, 100, 1, rng.gen_bool()),
        3 => (1, 100, 1, rng.gen_bool()),
        4 => (100, 1, 1, rng.gen_bool()),
        5 => (2, 4, 1, rng.gen_bool()),
        6 => (2, 1, 1, rng.gen_bool()),
        7 => (10, 1, 1, rng.gen_bool()),
        8 => {
            let r = rng.gen_range_i32(1, 10);
            let b = rng.gen_range_i32(1, 10);
            (r, b, 1, rng.gen_bool())
        }
        9 => {
            let r = rng.gen_range_i32(1, 100);
            let b = rng.gen_range_i32(1, 100);
            (r, b, 1, rng.gen_bool())
        }
        _ => {
            let r = rng.gen_range_i32(1, 100);
            let b = rng.gen_range_i32(1, 100);
            (r, b, 1, rng.gen_bool())
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (red, blue, row, red_turn) = pick(&mut rng, mode);
        let (r, b, row_out, rt) = generate_test_case(red, blue, row, red_turn);
        println!("{{\"red\": {}, \"blue\": {}, \"row\": {}, \"red_turn\": {}}}",
            r, b, row_out, rt);
    }
}