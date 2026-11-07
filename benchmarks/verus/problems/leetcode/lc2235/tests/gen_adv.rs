use vstd::prelude::*;

verus! {

pub fn generate_test_case(num1: i32, num2: i32) -> (result: (i32, i32))
    requires
        -100 <= num1 <= 100,
        -100 <= num2 <= 100,
    ensures
        -100 <= result.0 <= 100,
        -100 <= result.1 <= 100,
{
    (num1, num2)
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (0, 0),
        1 => (100, 100),
        2 => (-100, -100),
        3 => (100, -100),
        4 => (-100, 100),
        5 => (rng.gen_range_i32(-100, 100), 0),
        6 => (0, rng.gen_range_i32(-100, 100)),
        7 => (1, -1),
        8 => (rng.gen_range_i32(-100, 100), 100),
        9 => (-100, rng.gen_range_i32(-100, 100)),
        _ => (rng.gen_range_i32(-100, 100), rng.gen_range_i32(-100, 100)),
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (a, b) = pick_for_mode(&mut rng, mode);
        let (n1, n2) = generate_test_case(a, b);
        println!("{{\"num1\":{},\"num2\":{}}}", n1, n2);
    }
}