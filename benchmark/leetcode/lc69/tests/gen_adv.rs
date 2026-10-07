use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32) -> (res: i32)
    requires
        0 <= x <= i32::MAX,
    ensures
        0 <= res <= i32::MAX,
{
    x
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
        (lo as i64 + v as i64) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4 => 4,
        5 => i32::MAX,
        6 => i32::MAX - 1,
        7 => {
            // perfect square
            let r = rng.gen_range_i32(0, 46340);
            r * r
        }
        8 => {
            // perfect square - 1
            let r = rng.gen_range_i32(1, 46340);
            r * r - 1
        }
        9 => {
            // perfect square + 1
            let r = rng.gen_range_i32(0, 46340);
            let v = r as i64 * r as i64 + 1;
            if v > i32::MAX as i64 { i32::MAX } else { v as i32 }
        }
        10 => rng.gen_range_i32(0, 100),
        11 => rng.gen_range_i32(0, 1_000_000),
        _ => rng.gen_range_i32(0, i32::MAX),
    }
}

fn print_json(x: i32) {
    println!("{{\"x\":{}}}", x);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let x = pick_for_mode(&mut rng, mode);
        let x = if x < 0 { 0 } else { x };
        let v = generate_test_case(x);
        print_json(v);
    }
}