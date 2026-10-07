use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32) -> (result: i32)
    requires
        0 <= n_val <= 8,
    ensures
        0 <= result <= 8,
{
    n_val
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 200usize;

    // Adversarial edge cases: all boundary values
    let edge_cases: Vec<i32> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    for t in 0..total {
        let n = if t < edge_cases.len() * 4 {
            edge_cases[t % edge_cases.len()]
        } else {
            let mode = t % 10;
            match mode {
                0 => 0,
                1 => 8,
                2 => 1,
                3 => 7,
                4 => 2,
                5 => 6,
                _ => rng.gen_range_i32(0, 8),
            }
        };

        let out = generate_test_case(n);
        println!("{{\"n\":{}}}", out);
    }
}