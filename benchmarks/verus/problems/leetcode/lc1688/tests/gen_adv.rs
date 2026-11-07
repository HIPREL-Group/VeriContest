use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 200,
    ensures
        1 <= result <= 200,
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
    let total = 220usize;

    // Boundary & adversarial cases
    let adversarial: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 14, 15, 16, 17,
        31, 32, 33, 63, 64, 65, 99, 100, 127, 128, 129,
        199, 200, 150, 175, 50, 25, 10,
    ];

    let mut count = 0usize;

    for &v in &adversarial {
        if count >= total { break; }
        let n = generate_test_case(v);
        println!("{{\"n\":{}}}", n);
        count += 1;
    }

    while count < total {
        let mode = count % 7;
        let n_raw: i32 = match mode {
            0 => 1,
            1 => 200,
            2 => rng.gen_range_i32(1, 10),
            3 => rng.gen_range_i32(190, 200),
            4 => {
                // power of 2
                let choices = [2, 4, 8, 16, 32, 64, 128];
                choices[(rng.next_u64() as usize) % choices.len()]
            }
            5 => {
                // power of 2 minus 1 (odd)
                let choices = [3, 7, 15, 31, 63, 127];
                choices[(rng.next_u64() as usize) % choices.len()]
            }
            _ => rng.gen_range_i32(1, 200),
        };
        let n = generate_test_case(n_raw);
        println!("{{\"n\":{}}}", n);
        count += 1;
    }
}