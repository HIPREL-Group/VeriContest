use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 100,
    ensures
        1 <= result <= 100,
{
    n
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 4,
        4 => 100,
        5 => 99,
        6 => rng.gen_range_i32(1, 10),
        7 => {
            // even numbers
            let k = rng.gen_range_i32(1, 50);
            2 * k
        }
        8 => {
            // odd numbers
            let k = rng.gen_range_i32(0, 49);
            2 * k + 1
        }
        9 => rng.gen_range_i32(1, 100),
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let mut n = pick_for_mode(&mut rng, mode);
        if n < 1 {
            n = 1;
        }
        if n > 100 {
            n = 100;
        }
        let result = generate_test_case(n);
        println!("{{\"n\":{}}}", result);
    }
}