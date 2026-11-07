use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 1000,
    ensures
        1 <= result <= 1000,
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
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

    let adversarial: [i32; 20] = [
        1, 2, 3, 4, 5, 6, 7, 8, 15, 16,
        17, 31, 32, 33, 100, 500, 999, 1000, 512, 256,
    ];

    for t in 0..total {
        let n: i32 = if t < adversarial.len() {
            adversarial[t]
        } else {
            let mode = t % 6;
            match mode {
                0 => rng.gen_range_i32(1, 10),
                1 => rng.gen_range_i32(1, 100),
                2 => rng.gen_range_i32(1, 1000),
                3 => rng.gen_range_i32(900, 1000),
                4 => rng.gen_range_i32(1, 5),
                _ => {
                    let k = rng.gen_range_i32(1, 10);
                    let base: i32 = 1 << k;
                    if base > 1000 { 1000 } else { base }
                }
            }
        };

        let validated = generate_test_case(n);
        println!("{{\"n\":{}}}", validated);
    }
}