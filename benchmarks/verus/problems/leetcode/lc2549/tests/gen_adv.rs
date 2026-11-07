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
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_n(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 100,
        4 => 99,
        5 => 4,
        6 => 5,
        7 => 50,
        8 => rng.gen_range_i32(1, 100),
        9 => rng.gen_range_i32(1, 10),
        _ => {
            let v = (t % 100) as i32 + 1;
            v
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_n(&mut rng, mode, t);
        let result = generate_test_case(n);
        println!("{{\"n\": {}}}", result);
    }
}