use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32) -> (res: i32)
    requires
        1 <= x <= 100,
    ensures
        1 <= res <= 100,
{
    x
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
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 100,
        2 => 10,
        3 => 18,
        4 => 23,
        5 => 99,
        6 => rng.gen_range_i32(1, 9),
        7 => rng.gen_range_i32(10, 99),
        8 => {
            // Harshad: pick from known small set
            let cands = [1, 2, 3, 10, 12, 18, 20, 21, 24, 27, 30, 36, 40, 42, 45, 48, 50, 54, 60, 63, 70, 72, 80, 81, 84, 90, 100];
            let i = (rng.next_u64() as usize) % cands.len();
            cands[i]
        }
        9 => {
            // likely non-Harshad
            let cands = [11, 13, 14, 15, 16, 17, 19, 22, 23, 25, 26, 28, 29, 31, 32, 34, 35, 37, 38, 39, 41, 43];
            let i = (rng.next_u64() as usize) % cands.len();
            cands[i]
        }
        _ => rng.gen_range_i32(1, 100),
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
        let x = pick_for_mode(&mut rng, mode);
        let x = if x < 1 { 1 } else if x > 100 { 100 } else { x };
        let out = generate_test_case(x);
        println!("{{\"x\":{}}}", out);
    }
}